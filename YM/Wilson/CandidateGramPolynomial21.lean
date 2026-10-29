import YM.Wilson.CandidateGramRoots21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Actual finite-complexity composite candidate Wilson roots

Each monomial is a finite product of the explicit SIX-plaquette SU(2)
Gram-root candidates R_ij.  The coefficient budget retains the true
factor 4^degree instead of silently replacing it by a regulator-uniform
constant.  This is a strict bounded-template source dictionary, not
the missing physical engineering-scale cancellation or RG analyticity.
-/

/-- A finite product of genuine SU(2) cross-plaquette Gram roots. -/
def candidateGramMonomial (U : GramPlaquette6 → SU2) :
    List RootFiber21 → ℝ
  | [] => 1
  | α :: rest => candidateGramRoot21 U α * candidateGramMonomial U rest

theorem candidate_gram_monomial_abs_le
    (U : GramPlaquette6 → SU2) (roots : List RootFiber21) :
    |candidateGramMonomial U roots| ≤ (4 : ℝ) ^ roots.length := by
  induction roots with
  | nil =>
      simp [candidateGramMonomial]
  | cons α rest ih =>
      change |candidateGramRoot21 U α * candidateGramMonomial U rest| ≤
        (4 : ℝ) ^ (rest.length + 1)
      rw [abs_mul, pow_succ]
      calc
        |candidateGramRoot21 U α| * |candidateGramMonomial U rest|
            ≤ 4 * |candidateGramMonomial U rest| :=
          mul_le_mul_of_nonneg_right (candidate_gram_root21_abs_le_four U α)
            (abs_nonneg _)
        _ ≤ 4 * (4 : ℝ) ^ rest.length :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (4 : ℝ) ^ rest.length * 4 := by ring

/-- An arbitrary fixed finite linear combination of composite SU(2)
Gram roots.  The template is an actual finite list of monomials. -/
def candidateGramPolynomial
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21) (coeff : T → ℂ) : ℂ :=
  ∑ t : T, coeff t * (candidateGramMonomial U (monomials t) : ℂ)

/-- No coefficient/template bound is postulated: the exact sum is kept. -/
def candidateGramPolynomialBudget
    {T : Type*} [Fintype T]
    (monomials : T → List RootFiber21) (coeff : T → ℂ) : ℝ :=
  ∑ t : T, ‖coeff t‖ * (4 : ℝ) ^ (monomials t).length

theorem candidate_gram_polynomial_budget_nonneg
    {T : Type*} [Fintype T]
    (monomials : T → List RootFiber21) (coeff : T → ℂ) :
    0 ≤ candidateGramPolynomialBudget monomials coeff := by
  unfold candidateGramPolynomialBudget
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (by norm_num) _)

/-- Composite Wilson-root polynomial bound; the number of monomials
and each monomial degree appear only through the explicit budget. -/
theorem candidate_gram_polynomial_bound
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21) (coeff : T → ℂ) :
    ‖candidateGramPolynomial U monomials coeff‖ ≤
      candidateGramPolynomialBudget monomials coeff := by
  calc
    ‖candidateGramPolynomial U monomials coeff‖ ≤
        ∑ t : T, ‖coeff t * (candidateGramMonomial U (monomials t) : ℂ)‖ := by
          exact norm_sum_le _ _
    _ = ∑ t : T,
          ‖coeff t‖ * ‖(candidateGramMonomial U (monomials t) : ℂ)‖ := by
            simp only [norm_mul]
    _ ≤ ∑ t : T,
          ‖coeff t‖ * (4 : ℝ) ^ (monomials t).length := by
            apply Finset.sum_le_sum
            intro t ht
            have hm :
                ‖(candidateGramMonomial U (monomials t) : ℂ)‖ ≤
                  (4 : ℝ) ^ (monomials t).length := by
              rw [Complex.norm_real, Real.norm_eq_abs]
              exact candidate_gram_monomial_abs_le U (monomials t)
            exact mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    _ = candidateGramPolynomialBudget monomials coeff := rfl

/-- The genuine finite polynomial in the SIX plaquette holonomies,
smeared by the physical Schwartz test evaluated at one position. -/
def candidateGramPolynomialSchwartzSource
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21) (coeff : T → ℂ)
    (position : Space4) (f : SchwartzMap Space4 ℂ) : ℂ :=
  f position * candidateGramPolynomial U monomials coeff

theorem candidate_gram_polynomial_schwartz_bound
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21) (coeff : T → ℂ)
    (position : Space4) (f : SchwartzMap Space4 ℂ) :
    ‖candidateGramPolynomialSchwartzSource U monomials coeff
        position f‖ ≤
      candidateGramPolynomialBudget monomials coeff *
        SchwartzMap.seminorm ℂ 0 0 f := by
  have hf : ‖f position‖ ≤ SchwartzMap.seminorm ℂ 0 0 f :=
    f.norm_le_seminorm ℂ position
  have hp := candidate_gram_polynomial_bound U monomials coeff
  calc
    ‖candidateGramPolynomialSchwartzSource U monomials coeff position f‖ =
        ‖f position‖ * ‖candidateGramPolynomial U monomials coeff‖ := by
          simp only [candidateGramPolynomialSchwartzSource, norm_mul]
    _ ≤ SchwartzMap.seminorm ℂ 0 0 f *
        candidateGramPolynomialBudget monomials coeff :=
          mul_le_mul hf hp (norm_nonneg _) (apply_nonneg _ _)
    _ = candidateGramPolynomialBudget monomials coeff *
        SchwartzMap.seminorm ℂ 0 0 f := by ring

/-- True linearity of the tested composite polynomial in f. -/
theorem candidate_gram_polynomial_schwartz_sub
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21) (coeff : T → ℂ)
    (position : Space4) (f g : SchwartzMap Space4 ℂ) :
    candidateGramPolynomialSchwartzSource U monomials coeff
        position (f - g) =
      candidateGramPolynomialSchwartzSource U monomials coeff
        position f -
      candidateGramPolynomialSchwartzSource U monomials coeff
        position g := by
  change (f position - g position) *
      candidateGramPolynomial U monomials coeff =
      f position * candidateGramPolynomial U monomials coeff -
      g position * candidateGramPolynomial U monomials coeff
  ring

end YMUIC.Wilson
