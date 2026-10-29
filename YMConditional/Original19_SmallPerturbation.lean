import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace YMUIC.Counterterm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The relative perturbation uses the SAME classical source map as the paper. -/
def relativePerturbation (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E) : E →L[ℝ] E :=
  (M0.symm : E →L[ℝ] E) * (M - (M0 : E →L[ℝ] E))

omit [CompleteSpace E] in
theorem source_factorization (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E) :
    (M0 : E →L[ℝ] E) * (1 + relativePerturbation M0 M) = M := by
  ext x
  simp [relativePerturbation, ContinuousLinearMap.mul_apply, map_add, map_sub]

omit [CompleteSpace E] in
theorem relativePerturbation_norm (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E) :
    ‖relativePerturbation M0 M‖ ≤
      ‖(M0.symm : E →L[ℝ] E)‖ * ‖M - (M0 : E →L[ℝ] E)‖ :=
  norm_mul_le _ _

/-- Neumann inverse, constructed rather than assumed. -/
def oneAddEquiv (A : E →L[ℝ] E) (hA : ‖A‖ ≤ (1 / 2 : ℝ)) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (-A) (by rw [norm_neg]; linarith))

@[simp] theorem oneAddEquiv_apply (A : E →L[ℝ] E)
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) (x : E) :
    oneAddEquiv A hA x = x + A x := by
  change ((1 : E →L[ℝ] E) - -A) x = _
  simp

/-- The inverse is the entire operator-valued series, not a finite truncation. -/
theorem oneAddEquiv_inverse_series (A : E →L[ℝ] E)
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) :
    Summable (fun n : ℕ => (-A) ^ n) ∧
      ((oneAddEquiv A hA).symm : E →L[ℝ] E) = ∑' n : ℕ, (-A) ^ n := by
  constructor
  · exact summable_geometric_of_norm_lt_one (by rw [norm_neg]; linarith)
  · rfl

theorem oneAddEquiv_inverse_norm (A : E →L[ℝ] E)
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) :
    ‖((oneAddEquiv A hA).symm : E →L[ℝ] E)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  let x := (oneAddEquiv A hA).symm y
  have heq : x + A x = y := by
    simpa only [oneAddEquiv_apply] using (oneAddEquiv A hA).apply_symm_apply y
  have hAx : ‖A x‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
    (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))
  have htri : ‖x‖ ≤ ‖y‖ + ‖A x‖ := by
    have hx : x = y - A x := by rw [← heq]; abel
    calc ‖x‖ = ‖y - A x‖ := congrArg norm hx
      _ ≤ ‖y‖ + ‖A x‖ := norm_sub_le _ _
  change ‖x‖ ≤ 2 * ‖y‖
  linarith

/-- A genuine equivalence whose forward operator is the supplied M. -/
def sourceStepEquiv (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E)
    (hA : ‖relativePerturbation M0 M‖ ≤ (1 / 2 : ℝ)) : E ≃L[ℝ] E :=
  (oneAddEquiv (relativePerturbation M0 M) hA).trans M0

@[simp] theorem sourceStepEquiv_coe (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E)
    (hA : ‖relativePerturbation M0 M‖ ≤ (1 / 2 : ℝ)) :
    (sourceStepEquiv M0 M hA : E →L[ℝ] E) = M := by
  ext x
  change M0 (oneAddEquiv (relativePerturbation M0 M) hA x) = M x
  rw [oneAddEquiv_apply]
  have hx := congrArg (fun F : E →L[ℝ] E => F x) (source_factorization M0 M)
  simpa using hx

theorem sourceStepEquiv_inverse_formula (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E)
    (hA : ‖relativePerturbation M0 M‖ ≤ (1 / 2 : ℝ)) :
    ((sourceStepEquiv M0 M hA).symm : E →L[ℝ] E) =
      (∑' n : ℕ, (-relativePerturbation M0 M) ^ n) * (M0.symm : E →L[ℝ] E) := by
  rw [← (oneAddEquiv_inverse_series (relativePerturbation M0 M) hA).2]
  rfl

theorem sourceStepEquiv_inverse_norm (M0 : E ≃L[ℝ] E) (M : E →L[ℝ] E)
    (hA : ‖relativePerturbation M0 M‖ ≤ (1 / 2 : ℝ)) :
    ‖((sourceStepEquiv M0 M hA).symm : E →L[ℝ] E)‖ ≤
      2 * ‖(M0.symm : E →L[ℝ] E)‖ := by
  have heq : ((sourceStepEquiv M0 M hA).symm : E →L[ℝ] E) =
      ((oneAddEquiv (relativePerturbation M0 M) hA).symm : E →L[ℝ] E) *
        (M0.symm : E →L[ℝ] E) := rfl
  rw [heq]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (oneAddEquiv_inverse_norm _ hA) (norm_nonneg _))

/- The cutoff, scale, volume and background can ALL be components of i.
The weak window is chosen before i, using the original one-sided modulus. -/
omit [CompleteSpace E] in
theorem uniform_relative_smallness {ι : Type*}
    (M0 : E ≃L[ℝ] E) (M : ι → ℝ → E →L[ℝ] E)
    (ω : ℝ → ℝ) {gMax : ℝ} (hgMax : 0 < gMax)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i g, 0 < g → g ≤ gMax → ‖M i g - (M0 : E →L[ℝ] E)‖ ≤ ω g) :
    ∃ gD : ℝ, 0 < gD ∧ gD ≤ gMax ∧
      ∀ i g, 0 < g → g ≤ gD →
        ‖relativePerturbation M0 (M i g)‖ ≤ (1 / 2 : ℝ) := by
  have ht : Tendsto (fun g => ‖(M0.symm : E →L[ℝ] E)‖ * ω g)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hω.const_mul ‖(M0.symm : E →L[ℝ] E)‖
  have hev : ∀ᶠ g in 𝓝[>] (0 : ℝ),
      ‖(M0.symm : E →L[ℝ] E)‖ * ω g < (1 / 2 : ℝ) :=
    ht (Iio_mem_nhds (by norm_num))
  obtain ⟨d, hd, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨min d gMax, lt_min hd hgMax, min_le_right _ _, ?_⟩
  intro i g hg hgd
  have hgm : g ≤ gMax := hgd.trans (min_le_right _ _)
  exact (relativePerturbation_norm M0 (M i g)).trans
    ((mul_le_mul_of_nonneg_left (hmod i g hg hgm) (norm_nonneg _)).trans
      (hsub ⟨hg, hgd.trans (min_le_left _ _)⟩).le)

end YMUIC.Counterterm
