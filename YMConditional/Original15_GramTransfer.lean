import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

set_option autoImplicit false

namespace YMUIC.ConditionalI7

open scoped BigOperators ComplexConjugate InnerProductSpace
open Complex

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable section

/-- Centering at the normalized physical vacuum. -/
def center (Ω x : H) : H := x - ⟪Ω, x⟫_ℂ • Ω

/-- The actual Gram quadratic form of a finite observable family. -/
def gramForm (v : ι → H) (T : H →L[ℂ] H) (s : Finset ι) (c : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * ⟪v i, T (v j)⟫_ℂ

/-- I7 is a named argument, not a project axiom or a proved theorem. -/
def I7Gram (v : ι → H) (T : H →L[ℂ] H) (η : ℝ) : Prop :=
  ∀ (s : Finset ι) (c : ι → ℂ),
    η * (gramForm v (ContinuousLinearMap.id ℂ H) s c).re ≤
      (gramForm v (ContinuousLinearMap.id ℂ H) s c - gramForm v T s c).re

theorem center_continuous (Ω : H) : Continuous (center Ω) := by
  exact continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)

theorem center_eq_self_of_orthogonal (Ω x : H) (hx : ⟪Ω, x⟫_ℂ = 0) :
    center Ω x = x := by simp [center, hx]

theorem center_finite_sum (Ω : H) (v : ι → H) (s : Finset ι) (c : ι → ℂ) :
    center Ω (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • center Ω (v i) := by
  simp only [center, inner_sum, inner_smul_right, Finset.sum_smul, smul_sub,
    smul_smul, Finset.sum_sub_distrib]

theorem gramForm_eq_inner (v : ι → H) (T : H →L[ℂ] H)
    (s : Finset ι) (c : ι → ℂ) :
    gramForm v T s c =
      ⟪∑ i ∈ s, c i • v i, T (∑ i ∈ s, c i • v i)⟫_ℂ := by
  simp only [gramForm, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gramForm_identity (v : ι → H) (s : Finset ι) (c : ι → ℂ) :
    (gramForm v (ContinuousLinearMap.id ℂ H) s c).re =
      ‖∑ i ∈ s, c i • v i‖ ^ 2 := by
  rw [gramForm_eq_inner]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem finite_transfer_bound_of_I7 (v : ι → H) (T : H →L[ℂ] H)
    (η : ℝ) (hI7 : I7Gram v T η) (s : Finset ι) (c : ι → ℂ) :
    (⟪∑ i ∈ s, c i • v i, T (∑ i ∈ s, c i • v i)⟫_ℂ).re ≤
      (1 - η) * ‖∑ i ∈ s, c i • v i‖ ^ 2 := by
  have h := hI7 s c
  rw [sub_re, gramForm_identity, gramForm_eq_inner] at h
  linarith

/-- Original inventory #15 (paper Theorem 10.1), on an arbitrary complex
physical Hilbert space. Density is the uncentered observable exhaustion;
the finite Gram forms are computed from the same centered vectors and T.
No infinite-dimensional contraction is assumed. -/
theorem original15_transfer_from_I7
    (Ω : H) (v : ι → H) (T : H →L[ℂ] H) (η : ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (hI7 : I7Gram (fun i => center Ω (v i)) T η) :
    ∀ f : H, ⟪Ω, f⟫_ℂ = 0 →
      (⟪f, T f⟫_ℂ).re ≤ (1 - η) * ‖f‖ ^ 2 := by
  have hfinite : ∀ x ∈ (Submodule.span ℂ (Set.range v) : Set H),
      (⟪center Ω x, T (center Ω x)⟫_ℂ).re ≤ (1 - η) * ‖center Ω x‖ ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    rw [← hc]
    change (⟪center Ω (∑ i ∈ c.support, c i • v i),
      T (center Ω (∑ i ∈ c.support, c i • v i))⟫_ℂ).re ≤
      (1 - η) * ‖center Ω (∑ i ∈ c.support, c i • v i)‖ ^ 2
    rw [center_finite_sum]
    exact finite_transfer_bound_of_I7 _ T η hI7 c.support c
  have hleft : Continuous (fun x : H => (⟪center Ω x, T (center Ω x)⟫_ℂ).re) :=
    Complex.continuous_re.comp ((center_continuous Ω).inner
      (T.continuous.comp (center_continuous Ω)))
  have hright : Continuous (fun x : H => (1 - η) * ‖center Ω x‖ ^ 2) :=
    continuous_const.mul ((center_continuous Ω).norm.pow 2)
  intro f hf
  have h := le_on_closure hfinite hleft.continuousOn hright.continuousOn (hdense f)
  simpa only [center_eq_self_of_orthogonal Ω f hf] using h

/-- The same theorem in the deficit form requested by I7, with exactly
its finite Gram hypothesis, not a new coercivity premise. -/
theorem original15_deficit_from_I7
    (Ω : H) (v : ι → H) (T : H →L[ℂ] H) (η : ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (hI7 : I7Gram (fun i => center Ω (v i)) T η)
    (f : H) (hf : ⟪Ω, f⟫_ℂ = 0) :
    η * ‖f‖ ^ 2 ≤ (⟪f, f - T f⟫_ℂ).re := by
  have h := original15_transfer_from_I7 Ω v T η hdense hI7 f hf
  simp only [inner_sub_right, sub_re]
  have hn : (⟪f, f⟫_ℂ).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  rw [hn]
  linarith

#print axioms original15_transfer_from_I7
#print axioms original15_deficit_from_I7

end

end YMUIC.ConditionalI7
