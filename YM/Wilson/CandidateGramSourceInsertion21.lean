import YM.Wilson.CandidateGramPolynomial21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Actual SU(2) external Wilson-root exponential insertion

The v124 source repair uses D(s) = exp(s O) - 1 for a bounded
composite SU(2) Wilson root O.  The source is the ACTUAL finite product
of candidate 21 plaquette Gram roots.  Here we establish an explicit
nonzero complex-source radius using the genuine coefficient budget.

This establishes only the local insertion's finite bound.  It does not
prove the rooted cluster hypothesis or the actual quantum RG source map.
-/

/-- The actual exponential source insertion of a composite Gram
Wilson-root polynomial in a complex source parameter s. -/
def candidateGramSourceInsertion
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21)
    (coeff : T → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (s * candidateGramPolynomial U monomials coeff) - 1

/-- A positive source radius can be chosen only from the template's
EXPLICIT finite root budget, not from the UV lattice volume. -/
theorem candidate_gram_insertion_small_source
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21)
    (coeff : T → ℂ) (s : ℂ)
    (hsmall : ‖s‖ * candidateGramPolynomialBudget monomials coeff ≤ 1) :
    ‖candidateGramSourceInsertion U monomials coeff s‖ ≤
      2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff := by
  have hp : ‖candidateGramPolynomial U monomials coeff‖ ≤
      candidateGramPolynomialBudget monomials coeff :=
    candidate_gram_polynomial_bound U monomials coeff
  have hz : ‖s * candidateGramPolynomial U monomials coeff‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hsmall
  calc
    ‖candidateGramSourceInsertion U monomials coeff s‖ ≤
        2 * ‖s * candidateGramPolynomial U monomials coeff‖ := by
          exact Complex.norm_exp_sub_one_le hz
    _ = 2 * (‖s‖ * ‖candidateGramPolynomial U monomials coeff‖) := by
          rw [norm_mul]
    _ ≤ 2 * (‖s‖ * candidateGramPolynomialBudget monomials coeff) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (by norm_num)
    _ = 2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff := by ring

/-- The small-radius source estimate uniformly survives arbitrary
regulators WHEN THE SAME finite template coefficient budget is bounded
uniformly.  The model-side normalization is not assumed derived. -/
theorem candidate_gram_insertion_all_regulators
    {Regulator T : Type*} [Fintype T]
    (U : Regulator → GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21)
    (coeff : Regulator → T → ℂ)
    (K : ℝ) (_hK : 0 ≤ K)
    (hbudget : ∀ a, candidateGramPolynomialBudget monomials (coeff a) ≤ K)
    (s : ℂ) (hsmall : ‖s‖ * K ≤ 1) :
    ∀ a, ‖candidateGramSourceInsertion (U a) monomials (coeff a) s‖ ≤
      2 * ‖s‖ * K := by
  intro a
  have hsb : ‖s‖ * candidateGramPolynomialBudget monomials (coeff a) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (hbudget a) (norm_nonneg _)).trans hsmall
  calc
    _ ≤ 2 * ‖s‖ * candidateGramPolynomialBudget monomials (coeff a) :=
      candidate_gram_insertion_small_source (U a) monomials (coeff a) s hsb
    _ ≤ 2 * ‖s‖ * K := by
      exact mul_le_mul_of_nonneg_left (hbudget a) (by positivity)

end YMUIC.Wilson
