import YMOriginal.Original24_B10FromU2Exp
import YMOriginal.Original24_ActualWordMarked

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open Set

/-!
# Original24: U1+U2 produce the marked fifth moment for ACTUAL SU(2) sources

This removes the prior need to assume a fifth-order post-R
remainder inequality: the actual finite-cutoff fifth Taylor
remainder is DERIVED from real C^5 source derivatives, the original
unmarked U1 R bound, finite SU2 Wilson-word insertion and the
U2 root/tree exponential COUNT.

The only new upstream U2 data are explicit UNMARKED rooted tree
counts at the correct native length; no marked-R, analytic radius
or hB10 conclusion is passed as a hypothesis.
-/

/-- From the actual U1 unmarked activity and U2 rooted tree COUNT,
derive the exponential fifth moment for the SU2 composite external
source. The factor 2|s|B is from genuine Wilson words. -/
theorem actual_marked_exponential_moment_from_U1_U2
    {P T Γ : Type*} [Fintype T] [Fintype Γ]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (unmarked : Γ → ℂ) (d : Γ → ℝ)
    (kappa mu A Ctree : ℝ)
    (hA : 0 ≤ A)
    (hunmarked : ∀ γ, ‖unmarked γ‖ ≤
      A * Real.exp (-kappa * d γ))
    (hU2tree : (∑ γ : Γ, Real.exp (-(kappa - mu) * d γ)) ≤ Ctree) :
    (∑ γ : Γ,
      ‖actualWordMarkedR U words coeff s unmarked γ‖ *
        Real.exp (mu * d γ)) ≤
      (2 * ‖s‖ * actualWilsonPolynomialBudget words coeff * A) *
        Ctree := by
  let B : ℝ := 2 * ‖s‖ * actualWilsonPolynomialBudget words coeff
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (actual_wilson_polynomial_budget_nonneg words coeff)
  have hSrc :
      ‖actualWilsonInsertion U words coeff s‖ ≤ B :=
    actual_wilson_insertion_bound U words coeff s hsmall
  have hterm (γ : Γ) :
      ‖actualWordMarkedR U words coeff s unmarked γ‖ *
        Real.exp (mu * d γ) ≤
      (B * A) * Real.exp (-(kappa - mu) * d γ) := by
    have htail : 0 ≤
        (A * Real.exp (-kappa * d γ)) * Real.exp (mu * d γ) :=
      mul_nonneg
        (mul_nonneg hA (Real.exp_pos _).le) (Real.exp_pos _).le
    have hexp : Real.exp (-kappa * d γ) *
        Real.exp (mu * d γ) =
        Real.exp (-(kappa - mu) * d γ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ‖actualWordMarkedR U words coeff s unmarked γ‖ *
          Real.exp (mu * d γ) =
        ‖actualWilsonInsertion U words coeff s‖ *
          (‖unmarked γ‖ * Real.exp (mu * d γ)) := by
          simp only [actualWordMarkedR, norm_mul]
          ring
      _ ≤ ‖actualWilsonInsertion U words coeff s‖ *
          ((A * Real.exp (-kappa * d γ)) *
            Real.exp (mu * d γ)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (hunmarked γ)
            (Real.exp_pos _).le
      _ ≤ B * ((A * Real.exp (-kappa * d γ)) *
            Real.exp (mu * d γ)) :=
          mul_le_mul_of_nonneg_right hSrc htail
      _ = (B * A) * Real.exp (-(kappa - mu) * d γ) := by
          rw [← mul_assoc, hexp]
          ring
  calc
    (∑ γ : Γ, ‖actualWordMarkedR U words coeff s unmarked γ‖ *
      Real.exp (mu * d γ)) ≤
      ∑ γ : Γ, (B * A) * Real.exp (-(kappa - mu) * d γ) := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact hterm γ
    _ = (B * A) *
      (∑ γ : Γ, Real.exp (-(kappa - mu) * d γ)) := by
        rw [Finset.mul_sum]
    _ ≤ (B * A) * Ctree :=
      mul_le_mul_of_nonneg_left hU2tree (mul_nonneg hB hA)
    _ = (2 * ‖s‖ * actualWilsonPolynomialBudget words coeff * A) *
      Ctree := rfl

/-- The ORIGINAL fourth-order local subtraction and fifth-order B10
remainder, now derived for a genuine finite Wilson external-root source
from U1 unmarked R + U2 counting + real C^5 test derivatives.

The displayed hline5 is a pure SOURCE-TEST derivative hypothesis,
not the desired fifth-order remainder. Its derivation from the
4D C_c^5 test chain rule remains a model/test dictionary step.
-/
theorem actual_U1_U2_fifth_Taylor_source
    {P T Γ : Type*} [Fintype T] [Fintype Γ]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (unmarked : Γ → ℂ) (d : Γ → ℝ)
    (kappa mu A Ctree : ℝ)
    (hA : 0 ≤ A) (hmu : 0 < mu)
    (hd : ∀ γ, 0 ≤ d γ)
    (hunmarked : ∀ γ, ‖unmarked γ‖ ≤
      A * Real.exp (-kappa * d γ))
    (hU2tree : (∑ γ : Γ,
      Real.exp (-(kappa - mu) * d γ)) ≤ Ctree)
    (line : Γ → ℝ → ℂ)
    (aJ aN Mf : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN) (hMf : 0 ≤ Mf)
    (hf : ∀ γ, ContDiffOn ℝ 5 (line γ) (Icc 0 1))
    (hline5 : ∀ γ (t : ℝ), t ∈ Icc 0 1 →
      ‖iteratedDerivWithin 5 (line γ) (Icc 0 1) t‖ ≤
        Mf * (aJ / aN) ^ 5 * (d γ)^5) :
    ‖finiteMarkedTaylorRemainder
      (actualWordMarkedR U words coeff s unmarked) line‖ ≤
      (5 * ((2 * ‖s‖ * actualWilsonPolynomialBudget words coeff * A) *
        Ctree) / mu ^ 5) * Mf * (aJ / aN) ^ 5 := by
  have hmoment := actual_marked_exponential_moment_from_U1_U2
    U words coeff s hsmall unmarked d kappa mu A Ctree
    hA hunmarked hU2tree
  simpa only [Fintype.sum_eq_sum_univ] using
    finite_B10_Taylor_from_U2_exponential
      (actualWordMarkedR U words coeff s unmarked) line d
      aJ aN Mf mu
      ((2 * ‖s‖ * actualWilsonPolynomialBudget words coeff * A) *
        Ctree) haJ haN hMf hmu hd hf hline5 hmoment

end YMUIC.Original24
