import YMOriginal.Original24_WilsonWordPolynomial
import Mathlib.Analysis.Normed.Ring.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.R7
open YMUIC.Original24
open YMUIC.Wilson

/-- Product of r genuine bounded Wilson-word polynomial roots.
This is the coefficient obtained by taking one source derivative
in each of r independent external-root directions at J=0. -/
def actualWilsonExternalRootProduct
    {P T : Type*} [Fintype T]
    (r : ℕ) (U : P → SU2)
    (monomials : Fin r → T → List (List P))
    (coeff : Fin r → T → ℂ) : ℂ :=
  ∏ i : Fin r, actualWilsonPolynomial U (monomials i) (coeff i)

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
  unfold actualWilsonExternalRootProduct
  calc
    ‖∏ i : Fin r, actualWilsonPolynomial U (monomials i) (coeff i)‖
        ≤ ∏ i : Fin r, ‖actualWilsonPolynomial U (monomials i) (coeff i)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ i : Fin r, actualWilsonPolynomialBudget
          (monomials i) (coeff i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
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
  calc
    ‖actualWilsonExternalRootProduct r U monomials coeff‖ ≤
        ∏ i : Fin r, actualWilsonPolynomialBudget
          (monomials i) (coeff i) :=
      actual_wilson_external_root_product_bound r U monomials coeff
    _ ≤ ∏ _i : Fin r, B := by
      apply Finset.prod_le_prod
      · intro i hi
        exact actual_wilson_polynomial_budget_nonneg (monomials i) (coeff i)
      · intro i hi
        exact hbudget i
    _ = B ^ r := by
      simp

#print axioms actual_wilson_external_root_product_bound
#print axioms actual_wilson_external_root_product_uniform_bound

end YMUIC.R7
