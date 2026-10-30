import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open Set

/-!
# B10 fifth-order Taylor residual on a genuine finite polymer family

Replace the post-R estimate hB10 (previously used directly) by
a DERIVATION from the fifth directional test derivative via Mathlib's
actual C^5 Taylor remainder theorem and the U2 fifth moment.

Each f_gamma is the actual test function along one 4D source-to-root
line t ↦ f(x_gamma + t*a_j*y_gamma). Proving that its fifth
iterated derivative obeys the displayed physical test bound is a
4D chain-rule/normalization dictionary, not an R-source analytic
stability assumption.

No fifth-order remainder estimate is a hypothesis. All gamma
coefficient sums are FINITE (matching the finite-cutoff polymer
construction) and the U2 fifth moment C5 is an explicit input.
-/

/-- The exact order-five scalar Taylor bound from C^5 derivatives.
In particular, 4! = 24 appears in the denominator. -/
theorem actual_taylor_four_fifth_remainder
    (f : ℝ → ℂ) (C : ℝ)
    (hf : ContDiffOn ℝ 5 f (Icc 0 1))
    (hC : ∀ t ∈ Icc (0:ℝ) 1,
      ‖iteratedDerivWithin 5 f (Icc 0 1) t‖ ≤ C) :
    ‖f 1 - taylorWithinEval f 4 (Icc 0 1) 0 1‖ ≤ C / 24 := by
  have h := taylor_mean_remainder_bound (f := f)
    (a := (0 : ℝ)) (b := 1) (x := 1) (n := 4)
    (by norm_num) hf (by norm_num)
    (by
      intro t ht
      simpa using hC t ht)
  simpa [Nat.factorial] using h

/-- The actual finite-cutoff marked source Taylor remainder, without
assuming the post-R fifth-order conclusion. -/
def finiteMarkedTaylorRemainder
    {Γ : Type*} [Fintype Γ]
    (K : Γ → ℂ) (line : Γ → ℝ → ℂ) : ℂ :=
  ∑ γ : Γ, K γ *
    (line γ 1 - taylorWithinEval (line γ) 4 (Icc 0 1) 0 1)

/-- Fifth-order B10 source localization from actual fifth directional
derivative bound and U2 weighted fifth moment, not hB10.
The physical scale a_j/a_n remains present exactly. -/
theorem finite_marked_taylor_from_fifth_moment
    {Γ : Type*} [Fintype Γ]
    (K : Γ → ℂ) (line : Γ → ℝ → ℂ)
    (d : Γ → ℝ)
    (aJ aN Mf C5 : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN)
    (hMf : 0 ≤ Mf)
    (_hd : ∀ γ, 0 ≤ d γ)
    (hf : ∀ γ, ContDiffOn ℝ 5 (line γ) (Icc 0 1))
    (hderiv : ∀ γ (t : ℝ), t ∈ Icc 0 1 →
      ‖iteratedDerivWithin 5 (line γ) (Icc 0 1) t‖ ≤
        Mf * (aJ / aN) ^ 5 * (d γ)^5)
    (hmoment : (∑ γ : Γ, ‖K γ‖ * (d γ)^5) ≤ C5) :
    ‖finiteMarkedTaylorRemainder K line‖ ≤
      C5 * Mf * (aJ / aN) ^ 5 / 24 := by
  have hscale : 0 ≤ (aJ / aN) ^ 5 := pow_nonneg (div_nonneg haJ haN.le) 5
  have hcoef : 0 ≤ Mf * (aJ / aN) ^ 5 / 24 := by
    exact div_nonneg (mul_nonneg hMf hscale) (by norm_num)
  have hterm (γ : Γ) :
      ‖line γ 1 - taylorWithinEval (line γ) 4 (Icc 0 1) 0 1‖ ≤
        (Mf * (aJ / aN) ^ 5 * (d γ)^5) / 24 := by
    exact actual_taylor_four_fifth_remainder (line γ)
      (Mf * (aJ / aN) ^ 5 * (d γ)^5)
      (hf γ) (hderiv γ)
  calc
    ‖finiteMarkedTaylorRemainder K line‖ ≤
      ∑ γ : Γ, ‖K γ *
        (line γ 1 - taylorWithinEval (line γ) 4 (Icc 0 1) 0 1)‖ :=
          norm_sum_le _ _
    _ = ∑ γ : Γ, ‖K γ‖ *
        ‖line γ 1 - taylorWithinEval (line γ) 4 (Icc 0 1) 0 1‖ := by
          simp only [norm_mul]
    _ ≤ ∑ γ : Γ, ‖K γ‖ *
        ((Mf * (aJ / aN) ^ 5 * (d γ)^5) / 24) := by
          apply Finset.sum_le_sum
          intro γ hγ
          exact mul_le_mul_of_nonneg_left (hterm γ) (norm_nonneg _)
    _ = (Mf * (aJ / aN) ^ 5 / 24) *
        (∑ γ : Γ, ‖K γ‖ * (d γ)^5) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro γ hγ
          ring
    _ ≤ (Mf * (aJ / aN) ^ 5 / 24) * C5 :=
      mul_le_mul_of_nonneg_left hmoment hcoef
    _ = C5 * Mf * (aJ / aN) ^ 5 / 24 := by ring

end YMUIC.Original24
