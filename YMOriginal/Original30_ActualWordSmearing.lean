import YM.Wilson.WeightedSmearing
import YMOriginal.Original24_WilsonWordPolynomial

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Physical finite-volume Wilson-word source with Schwartz smearing

For every local source label p, use an ACTUAL finite polynomial of
ordered noncommuting SU2 Wilson words, not a generic bounded complex
symbol. The physical Schwartz source is the normalized finite sum
   sum_p w_p f(x_p) O_p(U).
The norm is UNIFORM in number of p, UV cutoff, and volume when the
explicit geometric cubature sum and fixed-template coefficient budgets
are bounded. The estimates DO NOT assume a uniform bound on the
renormalized source mixing chart; the latter is still a separate
Yang--Mills RG model obligation. Also, an actual a-dependent source
normalization must be substituted into w_p and verified independently.
-/

/-- Actual finite-volume polynomial Wilson source with arbitrary physical
weights, locations and genuinely ordered SU(2) holonomy words. -/
def actualWordSchwartzSmearing
    {P W T : Type*} [Fintype P] [Fintype T]
    (w : P → ℂ) (position : P → Space4)
    (U : P → W → SU2)
    (words : P → T → List (List W))
    (coeff : P → T → ℂ)
    (f : SchwartzMap Space4 ℂ) : ℂ :=
  ∑ p : P, w p * (f (position p) *
    actualWilsonPolynomial (U p) (words p) (coeff p))

/-- Explicit uniform source estimate for all finite physical lattices.
No dimension-independent bound is invented: K and C are exact
coefficient/weight budgets of the actual finite regulator. -/
theorem actual_word_schwartz_smearing_bound
    {P W T : Type*} [Fintype P] [Fintype T]
    (w : P → ℂ) (position : P → Space4)
    (U : P → W → SU2)
    (words : P → T → List (List W))
    (coeff : P → T → ℂ)
    (f : SchwartzMap Space4 ℂ) (q : ℕ)
    (K C : ℝ) (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (hcubature : (∑ p : P,
      ‖w p‖ / (1 + ‖position p‖ ^ q)) ≤ C) :
    ‖actualWordSchwartzSmearing w position U words coeff f‖ ≤
      K * C * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) := by
  let S : ℝ :=
    SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ q 0 f
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hsingle (p : P) :
      ‖w p * (f (position p) *
        actualWilsonPolynomial (U p) (words p) (coeff p))‖ ≤
      (‖w p‖ / (1 + ‖position p‖ ^ q)) * (K * S) := by
    have hp0 : 0 < 1 + ‖position p‖ ^ q := by positivity
    have hfa : ‖f (position p)‖ ≤
        S / (1 + ‖position p‖ ^ q) := by
      apply (le_div_iff₀ hp0).mpr
      have hweight := schwartz_weighted_point_bound q f (position p)
      calc
        ‖f (position p)‖ * (1 + ‖position p‖ ^ q) =
            (1 + ‖position p‖ ^ q) * ‖f (position p)‖ := by ring
        _ ≤ S := by simpa only [S] using hweight
    have hO :
        ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ ≤ K :=
      (actual_wilson_polynomial_bound (U p) (words p) (coeff p)).trans
        (hbudget p)
    have hSO :
        ‖f (position p)‖ *
          ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ ≤
        (S / (1 + ‖position p‖ ^ q)) * K :=
      mul_le_mul hfa hO (norm_nonneg _)
        (div_nonneg hS hp0.le)
    calc
      ‖w p * (f (position p) *
          actualWilsonPolynomial (U p) (words p) (coeff p))‖ =
        ‖w p‖ * (‖f (position p)‖ *
          ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖) := by
          simp only [norm_mul]
      _ ≤ ‖w p‖ * ((S / (1 + ‖position p‖ ^ q)) * K) :=
        mul_le_mul_of_nonneg_left hSO (norm_nonneg _)
      _ = (‖w p‖ / (1 + ‖position p‖ ^ q)) * (K * S) := by ring
  calc
    ‖actualWordSchwartzSmearing w position U words coeff f‖ ≤
        ∑ p : P, ‖w p * (f (position p) *
          actualWilsonPolynomial (U p) (words p) (coeff p))‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ p : P,
        (‖w p‖ / (1 + ‖position p‖ ^ q)) * (K * S) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hsingle p
    _ = (∑ p : P, ‖w p‖ / (1 + ‖position p‖ ^ q)) * (K * S) := by
          rw [Finset.sum_mul]
    _ ≤ C * (K * S) :=
        mul_le_mul_of_nonneg_right hcubature (mul_nonneg hK hS)
    _ = K * C * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) := by
          dsimp [S]
          ring

/-- Identical coefficient and geometric cubature budgets may hold for
arbitrary regulator families with varying numbers of physical source
cells. The theorem does NOT assume an ℓ^infty pointwise source bound
for the entire sum. -/
theorem actual_word_schwartz_smearing_all_regulators
    {Regulator W T : Type*} [Fintype T]
    (P : Regulator → Type*) [∀ r, Fintype (P r)]
    (w : ∀ r, P r → ℂ)
    (position : ∀ r, P r → Space4)
    (U : ∀ r, P r → W → SU2)
    (words : ∀ r, P r → T → List (List W))
    (coeff : ∀ r, P r → T → ℂ)
    (f : SchwartzMap Space4 ℂ) (q : ℕ)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hbudget : ∀ r (p : P r),
      actualWilsonPolynomialBudget (words r p) (coeff r p) ≤ K)
    (hcubature : ∀ r, (∑ p : P r,
      ‖w r p‖ / (1 + ‖position r p‖ ^ q)) ≤ C) :
    ∀ r, ‖actualWordSchwartzSmearing
      (w r) (position r) (U r) (words r) (coeff r) f‖ ≤
      K * C * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) := by
  intro r
  exact actual_word_schwartz_smearing_bound
    (w r) (position r) (U r) (words r) (coeff r) f q K C
    hK hC (hbudget r) (hcubature r)

end YMUIC.Original30
