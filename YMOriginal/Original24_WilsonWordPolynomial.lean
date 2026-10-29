import YM.Wilson.WordSource

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24: arbitrary fixed-complexity SU(2) Wilson word polynomial roots

Unlike the independent 21-Gram-root candidate, this grammar includes any
finite sum of finite products of genuine ordered SU(2) Wilson words,
the actual class of bounded raw external roots in C29 Section 14.2
and Original24 Section 15.5.

All monomial counts, lengths and coefficients are EXPLICIT and finite;
their own coefficient budgets are not silently assumed regulator-uniform.
The formal result does not establish that normalized v111 source
coefficients are bounded after a^-d scaling or canonical jet mixing.
-/

/-- A finite product of actual noncommutative SU(2) Wilson words. -/
def actualWilsonMonomial {P : Type*}
    (U : P → SU2) : List (List P) → ℂ
  | [] => 1
  | word :: rest =>
      (wilsonWordRoot U word : ℂ) * actualWilsonMonomial U rest

theorem actual_wilson_monomial_bound
    {P : Type*} (U : P → SU2) (words : List (List P)) :
    ‖actualWilsonMonomial U words‖ ≤ (4 : ℝ) ^ words.length := by
  induction words with
  | nil =>
      simp [actualWilsonMonomial]
  | cons word rest ih =>
      change ‖(wilsonWordRoot U word : ℂ) *
          actualWilsonMonomial U rest‖ ≤ (4 : ℝ) ^ (rest.length + 1)
      rw [norm_mul, pow_succ]
      calc
        ‖(wilsonWordRoot U word : ℂ)‖ * ‖actualWilsonMonomial U rest‖
            ≤ 4 * ‖actualWilsonMonomial U rest‖ :=
          mul_le_mul_of_nonneg_right
            (wilson_word_root_norm_le_four U word) (norm_nonneg _)
        _ ≤ 4 * (4 : ℝ) ^ rest.length :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (4 : ℝ) ^ rest.length * 4 := by ring

/-- Fixed finite linear combination of genuine Wilson word monomials. -/
def actualWilsonPolynomial
    {P T : Type*} [Fintype T]
    (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ) : ℂ :=
  ∑ t : T, coeff t * actualWilsonMonomial U (monomials t)

/-- Exact observable complexity/coefficients budget. -/
def actualWilsonPolynomialBudget
    {P T : Type*} [Fintype T]
    (monomials : T → List (List P)) (coeff : T → ℂ) : ℝ :=
  ∑ t : T, ‖coeff t‖ * (4 : ℝ) ^ (monomials t).length

theorem actual_wilson_polynomial_budget_nonneg
    {P T : Type*} [Fintype T]
    (monomials : T → List (List P)) (coeff : T → ℂ) :
    0 ≤ actualWilsonPolynomialBudget monomials coeff := by
  unfold actualWilsonPolynomialBudget
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (by norm_num) _)

theorem actual_wilson_polynomial_bound
    {P T : Type*} [Fintype T]
    (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ) :
    ‖actualWilsonPolynomial U monomials coeff‖ ≤
      actualWilsonPolynomialBudget monomials coeff := by
  calc
    ‖actualWilsonPolynomial U monomials coeff‖ ≤
      ∑ t : T, ‖coeff t * actualWilsonMonomial U (monomials t)‖ :=
        norm_sum_le _ _
    _ = ∑ t : T,
        ‖coeff t‖ * ‖actualWilsonMonomial U (monomials t)‖ := by
          simp only [norm_mul]
    _ ≤ ∑ t : T, ‖coeff t‖ * (4 : ℝ) ^ (monomials t).length := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left
            (actual_wilson_monomial_bound U (monomials t))
            (norm_nonneg _)
    _ = actualWilsonPolynomialBudget monomials coeff := rfl

/-- True external source multiplier exp(s O)-1, O finite SU(2) word polynomial. -/
def actualWilsonInsertion
    {P T : Type*} [Fintype T]
    (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ) : ℂ :=
  Complex.exp (s * actualWilsonPolynomial U monomials coeff) - 1

theorem actual_wilson_insertion_bound
    {P T : Type*} [Fintype T]
    (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget monomials coeff ≤ 1) :
    ‖actualWilsonInsertion U monomials coeff s‖ ≤
      2 * ‖s‖ * actualWilsonPolynomialBudget monomials coeff := by
  have hp := actual_wilson_polynomial_bound U monomials coeff
  have hz : ‖s * actualWilsonPolynomial U monomials coeff‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hsmall
  calc
    ‖actualWilsonInsertion U monomials coeff s‖ ≤
      2 * ‖s * actualWilsonPolynomial U monomials coeff‖ :=
        Complex.norm_exp_sub_one_le hz
    _ = 2 * (‖s‖ * ‖actualWilsonPolynomial U monomials coeff‖) := by
      rw [norm_mul]
    _ ≤ 2 * (‖s‖ * actualWilsonPolynomialBudget monomials coeff) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (by norm_num)
    _ = 2 * ‖s‖ * actualWilsonPolynomialBudget monomials coeff := by ring

end YMUIC.Original24
