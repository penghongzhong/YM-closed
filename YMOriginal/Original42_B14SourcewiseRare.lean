import YMOriginal.Original42_B14VanishingDefect
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.Original42

open YMUIC.ConditionalI7

/-!
# B14 from genuinely sourcewise rare-event errors

For a fixed finite centered Wilson source family (s,c), a bad-field
probability may depend on the source and may go to zero only after
that source is fixed. No single global cutoff error err(k) is assumed.

This is a direct continuum-only refinement of the strictly compiled
Original42_B14VanishingDefect.lean theorem. It assumes no finite-regulator
I7, no physical bad-event estimate, no true Wilson IR contraction.
It verifies only the B14 sourcewise-limit deduction.
-/

/-- Asymptotic same-net Gram contraction implies a strictly positive
continuum generator gap even when *no* finite-cutoff exact I7 bound
has been established. The vanishing defect is source-dependent, absolute, and need only tend
to zero after the finite source family and coefficients are fixed. -/
theorem b14_continuum_gap_from_sourcewise_error
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
        (𝓝 (‖∑ j ∈ s, c j • v j‖ ^ 2)))
    (hQtlim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Qt k s c) l
        (𝓝 (⟪Tcont (∑ j ∈ s, c j • v j),
              ∑ j ∈ s, c j • v j⟫_ℂ).re))
    (err : Finset J → (J → ℂ) → Cut → ℝ)
    (herr0 : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (err s c) l (𝓝 0))
    (hcut : ∀ (s : Finset J) (c : J → ℂ),
      ∀ᶠ k in l, Qt k s c ≤ Real.exp (-t * d) * Q0 k s c +
        err s c k) :
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
    have herr :
        Tendsto (err s cf) l (𝓝 0) := herr0 s cf
    have hdiff :
        Tendsto
          (fun k => q * Q0 k s cf + err s cf k - Qt k s cf) l
          (𝓝 (q * ‖∑ j ∈ s, cf j • v j‖ ^ 2 -
            (⟪Tcont (∑ j ∈ s, cf j • v j),
              ∑ j ∈ s, cf j • v j⟫_ℂ).re)) := by
      simpa only [add_zero] using
        ((Filter.Tendsto.const_mul q h0).add herr).sub htlim
    have hnonneg :
        0 ≤ q * ‖∑ j ∈ s, cf j • v j‖ ^ 2 -
          (⟪Tcont (∑ j ∈ s, cf j • v j),
            ∑ j ∈ s, cf j • v j⟫_ℂ).re := by
      apply ge_of_tendsto hdiff
      exact (hcut s cf).mono
        (fun k hk => sub_nonneg.mpr hk)
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
  exact heq ▸ hzlower

#print axioms b14_continuum_gap_from_sourcewise_error

end YMUIC.Original42
