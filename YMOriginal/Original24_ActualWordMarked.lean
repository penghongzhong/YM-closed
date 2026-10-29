import YMOriginal.Original24_MarkedRootBridge
import YMOriginal.Original24_WilsonWordPolynomial

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Actual arbitrary finite Wilson-word external source under unmarked old/new R

This is the direct fixed-D bounded-root class required for the C29
Original24 statement, not the special independent 21-Gram candidate.

No composite-source deformation of old/new R is used. Existing U2
root-tree and U1 unmarked polymer data are explicit inputs.
-/

def actualWordMarkedR
    {P T Γ : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ) (unmarked : Γ → ℂ) (γ : Γ) : ℂ :=
  actualWilsonInsertion U words coeff s * unmarked γ

theorem actual_word_marked_r_sum
    {P T Γ : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (unmarked : Γ → ℂ) (treeWeight : Γ → ℝ)
    (mu cRt dRoot aAct : ℝ) (Nroot : ℕ)
    (htree : ∀ γ, 0 ≤ treeWeight γ)
    (hweighted : ∀ γ,
      Real.exp (mu * dRoot) * ‖unmarked γ‖ ≤
        Real.exp (mu * cRt) * treeWeight γ)
    (hsum : Summable treeWeight)
    (htotal : (∑' γ, treeWeight γ) ≤ (Nroot : ℝ) * aAct) :
    (∑' γ, ‖actualWordMarkedR U words coeff s unmarked γ‖) ≤
      (2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aAct * Real.exp (-mu * dRoot) := by
  let K : ℝ := 2 * ‖s‖ * actualWilsonPolynomialBudget words coeff
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (actual_wilson_polynomial_budget_nonneg words coeff)
  have hD : ‖actualWilsonInsertion U words coeff s‖ ≤ K :=
    actual_wilson_insertion_bound U words coeff s hsmall
  have hw (γ : Γ) :
      Real.exp (mu * dRoot) *
          ‖actualWordMarkedR U words coeff s unmarked γ‖ ≤
        K * Real.exp (mu * cRt) * treeWeight γ := by
    calc
      Real.exp (mu * dRoot) *
          ‖actualWordMarkedR U words coeff s unmarked γ‖ =
        ‖actualWilsonInsertion U words coeff s‖ *
          (Real.exp (mu * dRoot) * ‖unmarked γ‖) := by
          simp only [actualWordMarkedR, norm_mul]
          ring
      _ ≤ ‖actualWilsonInsertion U words coeff s‖ *
          (Real.exp (mu * cRt) * treeWeight γ) :=
        mul_le_mul_of_nonneg_left (hweighted γ) (norm_nonneg _)
      _ ≤ K * (Real.exp (mu * cRt) * treeWeight γ) :=
        mul_le_mul_of_nonneg_right hD
          (mul_nonneg (Real.exp_pos _).le (htree γ))
      _ = K * Real.exp (mu * cRt) * treeWeight γ := by ring
  exact one_root_tree_sum
    (fun γ => ‖actualWordMarkedR U words coeff s unmarked γ‖)
    treeWeight K mu cRt dRoot aAct Nroot
    (fun γ => norm_nonneg _) htree hK hw hsum htotal

theorem actual_word_old_new_r_marked
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
    (hboundNew : (∑' γ, treeNew γ) ≤ (Nroot : ℝ) * aNew) :
    (∑' γ, ‖actualWordMarkedR U words coeff s oldR γ‖) ≤
      (2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aOld * Real.exp (-mu * dRoot) ∧
    (∑' γ, ‖actualWordMarkedR U words coeff s newR γ‖) ≤
      (2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aNew * Real.exp (-mu * dRoot) := by
  exact ⟨
    actual_word_marked_r_sum U words coeff s hsmall oldR treeOld
      mu cRt dRoot aOld Nroot htreeOld hweightedOld hsumOld hboundOld,
    actual_word_marked_r_sum U words coeff s hsmall newR treeNew
      mu cRt dRoot aNew Nroot htreeNew hweightedNew hsumNew hboundNew⟩

end YMUIC.Original24
