import YMOriginal.Original24_TwoExternalWilsonRoots

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Actual two-composite-root C29 (316)--(317), full fixed source radius

Unlike the small-source-only certificate, this proves the exact
external-root source constant of manuscript Lemma 15.4:

 K_{p,q} = (exp(r B_p)-1)(exp(r B_q)-1)

for arbitrary fixed r>=0, both complex parameters |s|,|t|<=r
and actual finite SU2 Wilson-polynomial root budgets B_p, B_q.

No analyticity or source deformation of the bulk R operation occurs
as a model premise. The U2 nonnegative rooted-tree weight and its
counting bound are the stated published/model analysis interface.
The actual old/new-R history dictionary is still to be matched.
-/

/-- Genuine arbitrary-radius bound for the real SU2 Wilson-word
polynomial external source exp(s O)-1. -/
theorem actual_wilson_word_insertion_full_radius
    {P T : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ) (radius B : ℝ)
    (hr : 0 ≤ radius) (_hB : 0 ≤ B)
    (hs : ‖s‖ ≤ radius)
    (hbudget : actualWilsonPolynomialBudget words coeff ≤ B) :
    ‖actualWilsonInsertion U words coeff s‖ ≤
      Real.exp (radius * B) - 1 := by
  have hb : 0 ≤ actualWilsonPolynomialBudget words coeff :=
    actual_wilson_polynomial_budget_nonneg words coeff
  have hNorm :
      ‖s * actualWilsonPolynomial U words coeff‖ ≤ radius * B := by
    calc
      ‖s * actualWilsonPolynomial U words coeff‖ =
          ‖s‖ * ‖actualWilsonPolynomial U words coeff‖ := norm_mul _ _
      _ ≤ ‖s‖ * actualWilsonPolynomialBudget words coeff :=
          mul_le_mul_of_nonneg_left
            (actual_wilson_polynomial_bound U words coeff)
            (norm_nonneg _)
      _ ≤ radius * B :=
          mul_le_mul hs hbudget hb hr
  calc
    ‖actualWilsonInsertion U words coeff s‖ =
        ‖Complex.exp (s * actualWilsonPolynomial U words coeff) - 1‖ := rfl
    _ ≤ Real.exp ‖s * actualWilsonPolynomial U words coeff‖ - 1 :=
        (by
          simpa using
            Complex.norm_exp_sub_sum_le_exp_norm_sub_sum
              (s * actualWilsonPolynomial U words coeff) 1)
    _ ≤ Real.exp (radius * B) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hNorm) 1

/-- The mixed source factor has two independent full-radius constants.
The right side is NONNEGATIVE for Bp,Bq,r>=0. -/
theorem actual_two_root_insertion_full_radius
    {P T S : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq) :
    ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤
      (Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1) := by
  have hKp : 0 ≤ Real.exp (radius * Bp) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hr hp0)
    linarith
  change ‖actualWilsonInsertion U wp cp s *
    actualWilsonInsertion U wq cq t‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul
    (actual_wilson_word_insertion_full_radius U wp cp s
      radius Bp hr hp0 hs hp)
    (actual_wilson_word_insertion_full_radius U wq cq t
      radius Bq hr hq0 ht hq)
    (norm_nonneg _) hKp

/-- Original double-external-root v57 rooted sum with exactly
the (exp(r Bp)-1)(exp(r Bq)-1) constant, not a small-source surrogate. -/
theorem actual_two_root_full_radius_rooted_tree
    {P T S Γ : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (unmarked : Γ → ℂ) (treeWeight : Γ → ℝ)
    (mu cRt dRoot aAct : ℝ) (Nroot : ℕ)
    (htree : ∀ γ, 0 ≤ treeWeight γ)
    (hweighted : ∀ γ,
      Real.exp (mu * dRoot) * ‖unmarked γ‖ ≤
        Real.exp (mu * cRt) * treeWeight γ)
    (hsum : Summable treeWeight)
    (htotal : (∑' γ, treeWeight γ) ≤ (Nroot : ℝ) * aAct) :
    (∑' γ, ‖actualTwoRootMarkedR U wp cp wq cq s t
      unmarked γ‖) ≤
      ((Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aAct * Real.exp (-mu * dRoot) := by
  let K : ℝ :=
    (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
  have hKp : 0 ≤ Real.exp (radius * Bp) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hr hp0)
    linarith
  have hKq : 0 ≤ Real.exp (radius * Bq) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hr hq0)
    linarith
  have hK : 0 ≤ K := mul_nonneg hKp hKq
  have hD : ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤ K :=
    actual_two_root_insertion_full_radius U wp cp wq cq
      s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  have hw (γ : Γ) :
      Real.exp (mu * dRoot) *
        ‖actualTwoRootMarkedR U wp cp wq cq s t unmarked γ‖ ≤
          K * Real.exp (mu * cRt) * treeWeight γ := by
    calc
      Real.exp (mu * dRoot) *
        ‖actualTwoRootMarkedR U wp cp wq cq s t unmarked γ‖ =
          ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
            (Real.exp (mu * dRoot) * ‖unmarked γ‖) := by
              simp only [actualTwoRootMarkedR, norm_mul]
              ring
      _ ≤ ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
          (Real.exp (mu * cRt) * treeWeight γ) :=
            mul_le_mul_of_nonneg_left (hweighted γ) (norm_nonneg _)
      _ ≤ K * (Real.exp (mu * cRt) * treeWeight γ) :=
            mul_le_mul_of_nonneg_right hD
              (mul_nonneg (Real.exp_pos _).le (htree γ))
      _ = K * Real.exp (mu * cRt) * treeWeight γ := by ring
  exact one_root_tree_sum
    (fun γ => ‖actualTwoRootMarkedR U wp cp wq cq s t unmarked γ‖)
    treeWeight K mu cRt dRoot aAct Nroot
    (fun γ => norm_nonneg _) htree hK hw hsum htotal

end YMUIC.Original24
