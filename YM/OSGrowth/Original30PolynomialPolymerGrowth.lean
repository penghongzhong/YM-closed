import YM.OSGrowth.Polymer
import YM.OSGrowth.PolynomialMomentGrowth

set_option autoImplicit false
noncomputable section

open Metric Set

namespace YMUIC.OSGrowth

/-!
# Original30: finite genuine-polymer logarithm to single-factorial growth

This is a new assembly of earlier strictly checked conditional Mathlib
lemmas, but the input now explicitly includes finite polymer activities
and the rooted level counting on the SAME regulator.

CRITICAL: The analytic activity bound, its source radius and the
rooted polymer count are explicit hypotheses, not assumed proved for
the physical Yang--Mills renormalized source.  The conclusion concerns
a finite polymer log and its exactly normalized source exponential,
not yet the continuum Schwinger hierarchy.
-/

/-- Finite connected-polymer Cauchy/Schwinger assembly.  Shrinking the
source radius pays only (1+A)^r instead of exp(A), which is necessary
when A grows with the physical compact support. -/
theorem finite_polymer_polynomial_schwinger_growth
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [DecidableEq P]
    (s : Finset P) (a : P → E → ℂ) (τ : P → ℕ)
    {ρ κ σ ε C : ℝ}
    (hρ : 0 < ρ) (hκ : σ < κ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hanalytic : ∀ X ∈ s, AnalyticOnNhd ℂ (a X) (ball 0 ρ))
    (hcount : ∀ n,
      ((s.filter (fun X => τ X = n)).card : ℝ) ≤
        C * Real.exp (σ * n))
    (hweight : ∀ X ∈ s, ∀ J ∈ ball 0 ρ,
      ‖a X J‖ ≤ ε * Real.exp (-κ * τ X))
    {r : ℕ} (hr : 0 < r) (h : Fin r → E) :
    ‖iteratedFDeriv ℂ r (normalizedPartition (polymerLog s a)) 0 h‖ ≤
      Real.exp 1 *
        (2 * Real.exp 1 *
          (1 + ε * C / (1 - Real.exp (-(κ - σ)))) / ρ) ^ r *
        r.factorial * ∏ j, ‖h j‖ := by
  let A : ℝ := ε * C / (1 - Real.exp (-(κ - σ)))
  have hq : Real.exp (-(κ - σ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg hε hC) (by linarith)
  have ha : AnalyticOnNhd ℂ (polymerLog s a) (ball 0 ρ) :=
    polymerLog_analytic hanalytic
  have hb : ∀ J ∈ ball 0 ρ, ‖polymerLog s a J‖ ≤ A := by
    simpa only [A] using
      (polymerLog_bound (s := s) a τ hκ hε hC hcount hweight)
  exact local_moment_polynomial_growth hρ hA ha hb hr h

end YMUIC.OSGrowth
