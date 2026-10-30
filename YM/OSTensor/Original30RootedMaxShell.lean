import YM.OSGrowth.Polymer
import YM.OSTensor.MaxShellMoment

set_option autoImplicit false
noncomputable section

open Metric Set

namespace YMUIC.OSTensor
open YMUIC.OSGrowth

/-!
# Original30: rooted polymer entropy is absorbed by maximum-shell factor

The source log is the ACTUAL finite polymerLog, not an abstract W.
If its shell-N root-count budget is O(2^(4N)), the previous verified
polynomial-radius lemma yields O(2^(4rN)) single-factorial moments.

The model must still prove that actual YM renormalized source
coefficients realize this analytic polymer family with regulator-uniform
epsilon, rho, kappa, sigma, C, and a 4D root covering count.
-/

theorem finite_polymer_max_shell_schwinger_growth
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [DecidableEq P]
    {r : ℕ} (hr : 0 < r) (n : Fin r → ℕ)
    (s : Finset P) (a : P → E → ℂ) (τ : P → ℕ)
    {ρ κ σ ε C : ℝ}
    (hρ : 0 < ρ) (hκ : σ < κ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hanalytic : ∀ X ∈ s, AnalyticOnNhd ℂ (a X) (ball 0 ρ))
    (hcount : ∀ k,
      ((s.filter (fun X => τ X = k)).card : ℝ) ≤
        (C * (2 : ℝ) ^ (4 * Finset.univ.sup n)) *
          Real.exp (σ * k))
    (hweight : ∀ X ∈ s, ∀ J ∈ ball 0 ρ,
      ‖a X J‖ ≤ ε * Real.exp (-κ * τ X))
    (h : Fin r → E) :
    ‖iteratedFDeriv ℂ r (normalizedPartition (polymerLog s a)) 0 h‖ ≤
      (Real.exp 1 *
        (2 * Real.exp 1 *
          (1 + ε * C / (1 - Real.exp (-(κ - σ)))) / ρ) ^ r *
          r.factorial) *
        (2 : ℝ) ^ (4 * r * Finset.univ.sup n) *
          ∏ j, ‖h j‖ := by
  let A : ℝ := ε * C / (1 - Real.exp (-(κ - σ)))
  let t : ℝ := (2 : ℝ) ^ (4 * Finset.univ.sup n)
  have hden : 0 ≤ 1 - Real.exp (-(κ - σ)) := by
    have hlt : Real.exp (-(κ - σ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg hε hC) hden
  have hCt : 0 ≤ C * t := mul_nonneg hC (by positivity)
  have ha : AnalyticOnNhd ℂ (polymerLog s a) (ball 0 ρ) :=
    polymerLog_analytic hanalytic
  have hb : ∀ J ∈ ball 0 ρ,
      ‖polymerLog s a J‖ ≤ A * t := by
    intro J hJ
    have hp := polymerLog_bound (s := s) a τ hκ hε hCt hcount
      hweight J hJ
    have heq : ε * (C * t) / (1 - Real.exp (-(κ - σ))) =
        A * t := by
      dsimp [A]
      ring
    exact hp.trans_eq heq
  simpa only [A, t] using
    (max_shell_moment (r := r) (d := 4) hr
      hρ hA (polymerLog s a) h n ha hb)

end YMUIC.OSTensor
