import YM.Wilson.WordSource

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24 raw composite Wilson source: exact finite template bound

This implements a genuinely noncommutative SU(2) Wilson-word polynomial:
a finite complex linear combination of finite products of ordered
Wilson-word traces.  In particular, it does NOT restrict v124 roots
to the 21 independently reconstructed Gram candidates.

Only the bounded raw external-root/source insertion is established here.
The actual v122 fixed-D template dictionary, the original unmarked
large-field polymer estimates, the renormalized source scaling and the
B11 fifth-order localization remain separate model obligations.
-/

/-- A finite product of actual ordered SU(2) Wilson-word roots. -/
def wilsonWordMonomial {P : Type*} (U : P → SU2) :
    List (List P) → ℂ
  | [] => 1
  | w :: ws =>
      (wilsonWordRoot U w : ℂ) * wilsonWordMonomial U ws

theorem wilson_word_monomial_norm_le
    {P : Type*} (U : P → SU2) (ws : List (List P)) :
    ‖wilsonWordMonomial U ws‖ ≤ (4 : ℝ) ^ ws.length := by
  induction ws with
  | nil =>
      simp [wilsonWordMonomial]
  | cons w rest ih =>
      change
        ‖(wilsonWordRoot U w : ℂ) * wilsonWordMonomial U rest‖ ≤
          (4 : ℝ) ^ (w :: rest).length
      rw [norm_mul]
      calc
        ‖(wilsonWordRoot U w : ℂ)‖ *
            ‖wilsonWordMonomial U rest‖ ≤
          4 * ‖wilsonWordMonomial U rest‖ :=
            mul_le_mul_of_nonneg_right
              (wilson_word_root_norm_le_four U w) (norm_nonneg _)
        _ ≤ 4 * (4 : ℝ) ^ rest.length :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (4 : ℝ) ^ (w :: rest).length := by
            simp [pow_succ, mul_comm]

/-- Exact fixed-complexity Wilson-word polynomial observable. -/
def wilsonWordPolynomial
    {P T : Type*} [Fintype T]
    (U : P → SU2)
    (monomials : T → List (List P))
    (coeff : T → ℂ) : ℂ :=
  ∑ t : T, coeff t * wilsonWordMonomial U (monomials t)

/-- Explicit coefficient budget: no hidden volume/source norm. -/
def wilsonWordPolynomialBudget
    {P T : Type*} [Fintype T]
    (monomials : T → List (List P))
    (coeff : T → ℂ) : ℝ :=
  ∑ t : T, ‖coeff t‖ * (4 : ℝ) ^ (monomials t).length

theorem wilson_word_polynomial_budget_nonneg
    {P T : Type*} [Fintype T]
    (monomials : T → List (List P)) (coeff : T → ℂ) :
    0 ≤ wilsonWordPolynomialBudget monomials coeff := by
  unfold wilsonWordPolynomialBudget
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (by norm_num) _)

/-- Uniform bound from the actual SU(2) Wilson word structure. -/
theorem wilson_word_polynomial_bound
    {P T : Type*} [Fintype T] (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ) :
    ‖wilsonWordPolynomial U monomials coeff‖ ≤
      wilsonWordPolynomialBudget monomials coeff := by
  calc
    ‖wilsonWordPolynomial U monomials coeff‖ ≤
        ∑ t : T, ‖coeff t * wilsonWordMonomial U (monomials t)‖ := by
          exact norm_sum_le _ _
    _ = ∑ t : T,
          ‖coeff t‖ * ‖wilsonWordMonomial U (monomials t)‖ := by
            simp only [norm_mul]
    _ ≤ ∑ t : T,
          ‖coeff t‖ * (4 : ℝ) ^ (monomials t).length := by
            apply Finset.sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_left
              (wilson_word_monomial_norm_le U (monomials t))
              (norm_nonneg _)
    _ = wilsonWordPolynomialBudget monomials coeff := rfl

/-- v124 external insertion: the bulk polymer activity is NOT deformed. -/
def wilsonWordExternalRoot
    {P T : Type*} [Fintype T] (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ) : ℂ :=
  Complex.exp (s * wilsonWordPolynomial U monomials coeff) - 1

/-- Actual bounded composite-root insertion, with a source radius
depending only on the explicit finite template budget. -/
theorem wilson_word_external_root_small
    {P T : Type*} [Fintype T] (U : P → SU2)
    (monomials : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * wilsonWordPolynomialBudget monomials coeff ≤ 1) :
    ‖wilsonWordExternalRoot U monomials coeff s‖ ≤
      2 * ‖s‖ * wilsonWordPolynomialBudget monomials coeff := by
  have hp :
      ‖wilsonWordPolynomial U monomials coeff‖ ≤
        wilsonWordPolynomialBudget monomials coeff :=
    wilson_word_polynomial_bound U monomials coeff
  have hz : ‖s * wilsonWordPolynomial U monomials coeff‖ ≤ 1 := by
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hsmall
  calc
    ‖wilsonWordExternalRoot U monomials coeff s‖ ≤
        2 * ‖s * wilsonWordPolynomial U monomials coeff‖ := by
          exact Complex.norm_exp_sub_one_le hz
    _ = 2 * (‖s‖ * ‖wilsonWordPolynomial U monomials coeff‖) := by
          rw [norm_mul]
    _ ≤ 2 * (‖s‖ * wilsonWordPolynomialBudget monomials coeff) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
            (by norm_num)
    _ = 2 * ‖s‖ * wilsonWordPolynomialBudget monomials coeff := by ring

/-- The v124 bound holds for ALL regulators with the SAME finite
template budget.  It does not assume RG-normalized coefficients enjoy
this bound: a uniform physical coefficient dictionary is still needed. -/
theorem wilson_word_external_root_all_regulators
    {Regulator P T : Type*} [Fintype T]
    (U : Regulator → P → SU2)
    (monomials : T → List (List P))
    (coeff : Regulator → T → ℂ)
    (B r : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ a, wilsonWordPolynomialBudget monomials (coeff a) ≤ B)
    (hsmall : r * B ≤ 1)
    (s : ℂ) (hs : ‖s‖ ≤ r) :
    ∀ a, ‖wilsonWordExternalRoot (U a) monomials (coeff a) s‖ ≤
      2 * r * B := by
  intro a
  have hb : ‖s‖ * wilsonWordPolynomialBudget monomials (coeff a) ≤
      ‖s‖ * B :=
    mul_le_mul_of_nonneg_left (hbudget a) (norm_nonneg _)
  have hsB : ‖s‖ * B ≤ r * B :=
    mul_le_mul_of_nonneg_right hs hB
  have hrad : ‖s‖ * wilsonWordPolynomialBudget monomials (coeff a) ≤ 1 :=
    (hb.trans hsB).trans hsmall
  calc
    ‖wilsonWordExternalRoot (U a) monomials (coeff a) s‖ ≤
        2 * ‖s‖ * wilsonWordPolynomialBudget monomials (coeff a) :=
      wilson_word_external_root_small (U a) monomials (coeff a) s hrad
    _ = 2 * (‖s‖ * wilsonWordPolynomialBudget monomials (coeff a)) := by
          ring
    _ ≤ 2 * (‖s‖ * B) :=
          mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2 * (r * B) :=
          mul_le_mul_of_nonneg_left hsB (by norm_num)
    _ = 2 * r * B := by ring

end YMUIC.Wilson
