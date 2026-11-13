import YMOriginal.Original24_WilsonWordPolynomial
import Mathlib.Analysis.Normed.Ring.Basic

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace YMUIC.R7
open YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-- Product of r genuine bounded Wilson-word polynomial roots.
This is the coefficient obtained by taking one source derivative
in each of r independent external-root directions at J=0. -/
def actualWilsonExternalRootProduct
    {P T : Type*} [Fintype T]
    (r : ℕ) (U : P → SU2)
    (monomials : Fin r → T → List (List P))
    (coeff : Fin r → T → ℂ) : ℂ :=
  ∏ i : Fin r, actualWilsonPolynomial U (monomials i) (coeff i)

/-- Elementary finite-product comparison specialized to nonnegative
real budgets; written explicitly to avoid ordered-monoid inference. -/
theorem finite_product_le_of_pointwise
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i)
    (hab : ∀ i ∈ s, a i ≤ b i) :
    (∏ i ∈ s, a i) ≤ ∏ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.prod_insert his, Finset.prod_insert his]
      have hai : 0 ≤ a i := ha i (by simp)
      have hbi : 0 ≤ b i := hb i (by simp)
      have hi : a i ≤ b i := hab i (by simp)
      have htail : (∏ j ∈ s, a j) ≤ ∏ j ∈ s, b j := by
        apply ih
        · intro j hj
          exact ha j (by simp [hj])
        · intro j hj
          exact hb j (by simp [hj])
        · intro j hj
          exact hab j (by simp [hj])
      calc
        a i * (∏ j ∈ s, a j) ≤ b i * (∏ j ∈ s, a j) :=
          mul_le_mul_of_nonneg_right hi
            (Finset.prod_nonneg (fun j hj => ha j (by simp [hj])))
        _ ≤ b i * (∏ j ∈ s, b j) :=
          mul_le_mul_of_nonneg_left htail hbi

/-- Exact all-order external-root budget.  No post-R source
analyticity is used: every factor is a genuine finite Wilson-word
polynomial and the product estimate is purely algebraic. -/
theorem actual_wilson_external_root_product_bound
    {P T : Type*} [Fintype T]
    (r : ℕ) (U : P → SU2)
    (monomials : Fin r → T → List (List P))
    (coeff : Fin r → T → ℂ) :
    ‖actualWilsonExternalRootProduct r U monomials coeff‖ ≤
      ∏ i : Fin r, actualWilsonPolynomialBudget
        (monomials i) (coeff i) := by
  classical
  unfold actualWilsonExternalRootProduct
  calc
    ‖∏ i : Fin r, actualWilsonPolynomial U (monomials i) (coeff i)‖
        ≤ ∏ i : Fin r, ‖actualWilsonPolynomial U (monomials i) (coeff i)‖ :=
      Finset.norm_prod_le' Finset.univ
        (by
          by_cases h : r = 0
          · subst r
            simp
          · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero h)))
        _
    _ ≤ ∏ i : Fin r, actualWilsonPolynomialBudget
          (monomials i) (coeff i) := by
      apply finite_product_le_of_pointwise
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact actual_wilson_polynomial_budget_nonneg (monomials i) (coeff i)
      · intro i hi
        exact actual_wilson_polynomial_bound U (monomials i) (coeff i)

/-- Uniform-budget corollary: if every root has complexity budget at most B,
the r-fold coefficient is bounded by B^r. -/
theorem actual_wilson_external_root_product_uniform_bound
    {P T : Type*} [Fintype T]
    (r : ℕ) (U : P → SU2)
    (monomials : Fin r → T → List (List P))
    (coeff : Fin r → T → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ i : Fin r,
      actualWilsonPolynomialBudget (monomials i) (coeff i) ≤ B) :
    ‖actualWilsonExternalRootProduct r U monomials coeff‖ ≤ B ^ r := by
  classical
  calc
    ‖actualWilsonExternalRootProduct r U monomials coeff‖ ≤
        ∏ i : Fin r, actualWilsonPolynomialBudget
          (monomials i) (coeff i) :=
      actual_wilson_external_root_product_bound r U monomials coeff
    _ ≤ ∏ _i : Fin r, B := by
      apply finite_product_le_of_pointwise
      · intro i hi
        exact actual_wilson_polynomial_budget_nonneg (monomials i) (coeff i)
      · intro i hi
        exact hB
      · intro i hi
        exact hbudget i
    _ = B ^ r := by
      simp

#print axioms finite_product_le_of_pointwise
#print axioms actual_wilson_external_root_product_bound
#print axioms actual_wilson_external_root_product_uniform_bound

end YMUIC.R7
