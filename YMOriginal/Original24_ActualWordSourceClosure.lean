import YMOriginal.Original24_ActualWordMarked
import YMOriginal.Original24_PostRLocalization

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24 genuine bounded source class: all finite Wilson words

Combine actual finite SU2 Wilson word polynomial insertion, U2 rooted
unmarked activity bounds, and the B10 fifth-order Taylor/placement
ratio q<1. The post-R remainder is a DERIVED summable consequence.

The physical C29 roots, local counterterms and support/distance
dictionary must still be identified with these precisely quantified
abstract model inputs before promoting the original theorem 24.
-/

theorem actual_word_post_r_localization_summable
    {P T Γ : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (oldR newR : Γ → ℂ) (treeOld treeNew : Γ → ℝ)
    (mu cRt dRoot aOld aNew : ℝ) (Nroot : ℕ)
    (htreeOld : ∀ γ, 0 ≤ treeOld γ)
    (htreeNew : ∀ γ, 0 ≤ treeNew γ)
    (hweightedOld : ∀ γ,
      Real.exp (mu * dRoot) * ‖oldR γ‖ ≤
        Real.exp (mu * cRt) * treeOld γ)
    (hweightedNew : ∀ γ,
      Real.exp (mu * dRoot) * ‖newR γ‖ ≤
        Real.exp (mu * cRt) * treeNew γ)
    (hsumOld : Summable treeOld) (hsumNew : Summable treeNew)
    (hboundOld : (∑' γ, treeOld γ) ≤ (Nroot : ℝ) * aOld)
    (hboundNew : (∑' γ, treeNew γ) ≤ (Nroot : ℝ) * aNew)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (remainder : ℕ → ℂ)
    (hB10 : ∀ m, ‖remainder m‖ ≤
      ((∑' γ, ‖actualWordMarkedR U words coeff s oldR γ‖) +
        (∑' γ, ‖actualWordMarkedR U words coeff s newR γ‖)) *
          q ^ m) :
    Summable (fun m => ‖remainder m‖) ∧
      (∑' m, ‖remainder m‖) ≤
        ((2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
        (aOld + aNew) * Real.exp (-mu * dRoot)) / (1 - q) := by
  let K : ℝ := 2 * ‖s‖ * actualWilsonPolynomialBudget words coeff
  let M : ℝ :=
    K * Real.exp (mu * cRt) * (Nroot : ℝ) *
      (aOld + aNew) * Real.exp (-mu * dRoot)
  obtain ⟨hOld, hNew⟩ :=
    actual_word_old_new_r_marked U words coeff s hsmall
      oldR newR treeOld treeNew mu cRt dRoot aOld aNew Nroot
      htreeOld htreeNew hweightedOld hweightedNew
      hsumOld hsumNew hboundOld hboundNew
  have hboth :
      (∑' γ, ‖actualWordMarkedR U words coeff s oldR γ‖) +
        (∑' γ, ‖actualWordMarkedR U words coeff s newR γ‖) ≤ M := by
    calc
      _ ≤
        (K * Real.exp (mu * cRt) * (Nroot : ℝ) * aOld *
          Real.exp (-mu * dRoot)) +
        (K * Real.exp (mu * cRt) * (Nroot : ℝ) * aNew *
          Real.exp (-mu * dRoot)) :=
          add_le_add hOld hNew
      _ = M := by dsimp [M, K]; ring
  have hrem (m : ℕ) : ‖remainder m‖ ≤ M * q ^ m :=
    (hB10 m).trans
      (mul_le_mul_of_nonneg_right hboth (pow_nonneg hq0 _))
  simpa only [M, K] using
    finite_marked_remainder_geometric q M hq0 hq1 remainder hrem

end YMUIC.Original24
