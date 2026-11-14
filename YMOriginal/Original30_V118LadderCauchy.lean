import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30

/-!
# v118 two-parameter weak-stop Cauchy assembly

This is the exact logical order used by the D=4 renormalized Schwinger
ladder:
  1. choose the old-history age R so the uniform old tail is small;
  2. keep R fixed;
  3. send the weak-stop index n to infinity so the recent small-field and large-field
     errors is small.

No Yang--Mills estimate is manufactured here.  The theorem only assembles
the two quantitative inputs, and it works for the actual complex connected
functional once those inputs are supplied by v105/v109/v110/v114.
-/

/-- Quantitative Cauchy criterion from the v118 old/recent decomposition.
The recent error is allowed to depend arbitrarily on the fixed age R. -/
theorem v118_two_parameter_ladder_cauchy_criterion
    (S : ℕ → ℂ)
    (oldTail : ℕ → ℝ)
    (recentTail : ℕ → ℕ → ℝ)
    (hbound : ∀ m n R : ℕ, m < n →
      ‖S m - S n‖ ≤ oldTail R + recentTail R n)
    (hOldSmall : ∀ ε : ℝ, 0 < ε →
      ∃ R : ℕ, oldTail R < ε)
    (hRecentSmall : ∀ R : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → recentTail R n < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        ‖S m - S n‖ < ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hOldSmall (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hRecentSmall R (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro m n hm hn
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · exact (hbound m n R hmn).trans_lt (by
      have hr := hN n hn
      linarith)
  · subst n
    simpa using hε
  · have hb := hbound n m R hmn
    have hr := hN m hm
    have hs : ‖S m - S n‖ = ‖S n - S m‖ := by
      rw [norm_sub_rev]
    rw [hs]
    exact hb.trans_lt (by linarith)

/-- The same criterion with the v118 decomposition written explicitly as
old + recent-small-field + recent-large-field. -/
theorem v118_three_channel_ladder_cauchy_criterion
    (S : ℕ → ℂ)
    (oldTail : ℕ → ℝ)
    (recentSF recentLF : ℕ → ℕ → ℝ)
    (hbound : ∀ m n R : ℕ, m < n →
      ‖S m - S n‖ ≤
        oldTail R + recentSF R n + recentLF R n)
    (hOldSmall : ∀ ε : ℝ, 0 < ε →
      ∃ R : ℕ, oldTail R < ε)
    (hRecentSF : ∀ R : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → recentSF R n < ε)
    (hRecentLF : ∀ R : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → recentLF R n < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        ‖S m - S n‖ < ε := by
  apply v118_two_parameter_ladder_cauchy_criterion
    S oldTail (fun R n => recentSF R n + recentLF R n)
  · intro m n R hmn
    simpa [add_assoc] using hbound m n R hmn
  · exact hOldSmall
  · intro R ε hε
    obtain ⟨Nsf, hNsf⟩ := hRecentSF R (ε / 2) (by linarith)
    obtain ⟨Nlf, hNlf⟩ := hRecentLF R (ε / 2) (by linarith)
    refine ⟨max Nsf Nlf, ?_⟩
    intro n hn
    have hsf := hNsf n (le_trans (le_max_left _ _) hn)
    have hlf := hNlf n (le_trans (le_max_right _ _) hn)
    linarith

#print axioms v118_two_parameter_ladder_cauchy_criterion
#print axioms v118_three_channel_ladder_cauchy_criterion

end YMUIC.Original30
