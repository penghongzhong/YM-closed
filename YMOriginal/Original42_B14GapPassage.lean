import YMConditional.Original16_FromI7
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.Original42
open YMUIC.ConditionalI7

/-!
# B14 continuum gap passage from entrywise finite-family limits

This is the non-goal-shaped producer behind manuscript item B14.
It never identifies Hilbert spaces at different cutoffs. For each
finite family and coefficient vector it only passes the scalar Gram
quadratic-form inequality through the same cutoff/volume filter, then
extends the resulting continuum form inequality from the finite span
to its Hilbert closure.
-/

/-- Entrywise/joint moment convergence of finite Gram forms preserves a
uniform heat-semigroup contraction and therefore the generator gap.

Q0 and Qt are cutoff scalar Gram quadratic forms. Their limits are
identified directly with the continuum Hilbert norm and continuum transfer
quadratic form. Thus no cross-cutoff vector comparison is used. -/
theorem b14_continuum_gap_from_joint_gram_limits
    {Cut J H : Type*} {l : Filter Cut} [l.NeBot]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : J → H)
    (Tcont : H →L[ℂ] H)
    (Acont : H →ₗ.[ℂ] H)
    (t d : ℝ) (ht : 0 < t) (hd : 0 < d)
    (hcalc : NonnegativeHeatCalculus Acont t Tcont)
    (hdense : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (Q0 Qt : Cut → Finset J → (J → ℂ) → ℝ)
    (hQ0lim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Q0 k s c) l
        (𝓝 ‖∑ j ∈ s, c j • v j‖ ^ 2))
    (hQtlim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Qt k s c) l
        (𝓝 (⟪Tcont (∑ j ∈ s, c j • v j),
              ∑ j ∈ s, c j • v j⟫_ℂ).re))
    (hcut : ∀ (k : Cut) (s : Finset J) (c : J → ℂ),
      Qt k s c ≤ Real.exp (-t * d) * Q0 k s c) :
    ((d : ℝ) : EReal) ≤ generatorGap Acont := by
  let q : ℝ := Real.exp (-t * d)
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos ht hd]
  have hfinite :
      ∀ x ∈ (Submodule.span ℂ (Set.range v) : Set H),
        (⟪Tcont x, x⟫_ℂ).re ≤ q * ‖x‖ ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    rw [← hc]
    let cf : J → ℂ := fun j => c j
    let s : Finset J := c.support
    have h0 := hQ0lim s cf
    have htlim := hQtlim s cf
    have hdiff :
        Tendsto
          (fun k => q * Q0 k s cf - Qt k s cf) l
          (𝓝 (q * ‖∑ j ∈ s, cf j • v j‖ ^ 2 -
            (⟪Tcont (∑ j ∈ s, cf j • v j),
              ∑ j ∈ s, cf j • v j⟫_ℂ).re)) :=
      (h0.const_mul q).sub htlim
    have hnonneg :
        0 ≤ q * ‖∑ j ∈ s, cf j • v j‖ ^ 2 -
          (⟪Tcont (∑ j ∈ s, cf j • v j),
            ∑ j ∈ s, cf j • v j⟫_ℂ).re := by
      apply ge_of_tendsto hdiff
      exact Filter.Eventually.of_forall (fun k => sub_nonneg.mpr (hcut k s cf))
    exact sub_nonneg.mp hnonneg
  have hleft : Continuous (fun x : H => (⟪Tcont x, x⟫_ℂ).re) :=
    Complex.continuous_re.comp (Tcont.continuous.inner continuous_id)
  have hright : Continuous (fun x : H => q * ‖x‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  have hform : ∀ x : H,
      (⟪Tcont x, x⟫_ℂ).re ≤ q * ‖x‖ ^ 2 := by
    intro x
    exact le_on_closure hfinite hleft.continuousOn hright.continuousOn
      (hdense x)
  have hg := original16_generator_gap Acont Tcont t q
    ht hq0 hq1 (hcalc.toHeatSpectralInput ht) hform
  apply generatorGap_lower Acont d
  intro z hz
  have hzlower := (hg.2 z hz).2
  have heq : -Real.log q / t = d := by
    dsimp [q]
    rw [Real.log_exp]
    field_simp [ne_of_gt ht]
    ring
  exact heq ▸ hzlower

#print axioms b14_continuum_gap_from_joint_gram_limits

end YMUIC.Original42
