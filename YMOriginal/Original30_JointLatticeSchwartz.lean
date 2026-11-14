import YMOriginal.Original30_ActualWordPhysicalBox
import YMOriginal.Original34_OSII_ExternalInterface

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Full JOINT Schwartz 4r-variable finite-cutoff Wilson distributions

This is a genuinely joint-test construction, not a theorem about
factorized tensors of 4D test functions. For each actual finite SU2
configuration and family of local finite Wilson word polynomials, form

  a^(4r) Sum_{(p_1,...,p_r) ∈ Plaquettes^r}
             f(x_{p_1},...,x_{p_r}) * Product_j O_{p_j}(U).

The full 4r-variable Schwartz test f is evaluated in a single step
and need not factorize. Every coefficient has the actual finite
noncommuting SU2 Wilson word observable, with an explicit template
coefficient budget; the source weight is the physical a^4.

For a physical box Na<=R, we obtain a cutoff-independent bound
  ||S_{r,a}(f)|| <= (6 K R^4)^r p_(0,0)(f)
where K is the fixed-template coefficient budget. This bound holds
for any family of source positions in the joint Euclidean space and
any SU2 link configuration, with no volume or UV cutoff in the RHS.

IMPORTANT: R here is a FIXED finite physical box, not an infinite
volume uniform constant. The a^4-weighted Wilson roots are not
automatically the renormalized F² or fixed-D observables of C29.
This does NOT prove the missing infinite-volume physical E0prime
or its source mixing/jet normalization.
-/

/-- One exact finite-cutoff joint 4r-dimensional Wilson-word source. -/
def actualWordJointCutoff
    {P W T : Type*} [Fintype P] [Fintype T]
    (r : ℕ)
    (weights : P → ℂ)
    (U : P → W → SU2)
    (words : P → T → List (List W))
    (coeff : P → T → ℂ)
    (locations : (Fin r → P) →
      EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r) : ℂ :=
  ∑ tuple : Fin r → P,
    (∏ j : Fin r,
      weights (tuple j) *
        actualWilsonPolynomial (U (tuple j))
          (words (tuple j)) (coeff (tuple j))) *
    f (locations tuple)

/-- For arbitrary finite source families, the JOINT Schwartz source
has explicit tensor-power growth (the f is not a pure tensor). -/
theorem actual_word_joint_cutoff_schwartz_bound
    {P W T : Type*} [Fintype P] [Fintype T]
    (r : ℕ)
    (weights : P → ℂ)
    (U : P → W → SU2)
    (words : P → T → List (List W))
    (coeff : P → T → ℂ)
    (locations : (Fin r → P) →
      EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r)
    (weightBound K : ℝ)
    (hwPos : 0 ≤ weightBound)
    (hKPos : 0 ≤ K)
    (hw : ∀ p, ‖weights p‖ ≤ weightBound)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    ‖actualWordJointCutoff r weights U words coeff locations f‖ ≤
      (((Fintype.card P : ℝ) * weightBound * K) ^ r) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  have hentry (p : P) :
      ‖weights p * actualWilsonPolynomial (U p)
        (words p) (coeff p)‖ ≤ weightBound * K := by
    rw [norm_mul]
    exact mul_le_mul (hw p)
      ((actual_wilson_polynomial_bound (U p) (words p) (coeff p)).trans
        (hbudget p))
      (norm_nonneg _) hwPos
  have hprod (tuple : Fin r → P) :
      ‖∏ j : Fin r,
        weights (tuple j) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))‖ ≤
        (weightBound * K) ^ r := by
    rw [norm_prod]
    calc
      (∏ j : Fin r,
        ‖weights (tuple j) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))‖) ≤
        ∏ _j : Fin r, (weightBound * K) := by
          exact Finset.prod_le_prod₀
            (fun j hj => norm_nonneg _)
            (fun j hj => hentry (tuple j))
      _ = (weightBound * K) ^ r := by simp
  have hterm (tuple : Fin r → P) :
      ‖(∏ j : Fin r, weights (tuple j) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))) *
        f (locations tuple)‖ ≤
      (weightBound * K) ^ r *
        SchwartzMap.seminorm ℂ 0 0 f := by
    rw [norm_mul]
    exact mul_le_mul (hprod tuple)
      (f.norm_le_seminorm ℂ (locations tuple))
      (norm_nonneg _) (pow_nonneg (mul_nonneg hwPos hKPos) _)
  calc
    ‖actualWordJointCutoff r weights U words coeff locations f‖ ≤
      ∑ tuple : Fin r → P,
        ‖(∏ j : Fin r, weights (tuple j) *
            actualWilsonPolynomial (U (tuple j))
              (words (tuple j)) (coeff (tuple j))) *
          f (locations tuple)‖ := norm_sum_le _ _
    _ ≤ ∑ _tuple : Fin r → P,
        (weightBound * K) ^ r *
          SchwartzMap.seminorm ℂ 0 0 f := by
        apply Finset.sum_le_sum
        intro tuple htuple
        exact hterm tuple
    _ = (((Fintype.card P : ℝ) * weightBound * K) ^ r) *
          SchwartzMap.seminorm ℂ 0 0 f := by
        simp [Fintype.card_fin, mul_pow]
        ring

/-- Actual physical 4D periodic box: P=6*N^4 plaquettes and each source
has EXACT a^4 volume weight. No additional geometric cubature budget
is assumed. The result applies to any genuine joint 4r Schwartz f. -/
theorem actual_word_joint_physical_box_bound
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a R : ℝ)
    (ha : 0 ≤ a) (_hR : 0 ≤ R)
    (hbox : (N : ℝ) * a ≤ R)
    (U : WilsonBoxPlaquettes N → W → SU2)
    (words : WilsonBoxPlaquettes N → T → List (List W))
    (coeff : WilsonBoxPlaquettes N → T → ℂ)
    (locations : (Fin r → WilsonBoxPlaquettes N) →
      EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    ‖actualWordJointCutoff r
      (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff locations f‖ ≤
      (6 * K * R ^ 4) ^ r * SchwartzMap.seminorm ℂ 0 0 f := by
  have hw (p : WilsonBoxPlaquettes N) :
      ‖((a ^ 4 : ℝ) : ℂ)‖ ≤ a ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ha 4)]
  have hraw := actual_word_joint_cutoff_schwartz_bound r
    (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U words coeff locations f (a ^ 4) K
    (pow_nonneg ha 4) hK hw hbudget
  have hvol : ((N : ℝ) * a) ^ 4 ≤ R ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) ha)
      hbox 4
  have hcoord :
      ((Fintype.card (WilsonBoxPlaquettes N) : ℝ) * a ^ 4 * K)
        ≤ 6 * K * R ^ 4 := by
    have hcount :
        (Fintype.card (WilsonBoxPlaquettes N) : ℝ) =
          6 * (N : ℝ) ^ 4 := by
      change (Fintype.card (Fin 6 × Fin (N ^ 4)) : ℝ) =
        6 * (N : ℝ) ^ 4
      simp only [Fintype.card_prod, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hident :
        ((Fintype.card (WilsonBoxPlaquettes N) : ℝ) * a ^ 4 * K) =
          6 * (((N : ℝ) * a) ^ 4) * K := by
      rw [hcount]
      ring
    rw [hident]
    calc
      6 * (((N : ℝ) * a) ^ 4) * K ≤ 6 * R ^ 4 * K :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvol (by norm_num)) hK
      _ = 6 * K * R ^ 4 := by ring
  have hb0 : 0 ≤
      ((Fintype.card (WilsonBoxPlaquettes N) : ℝ) * a ^ 4 * K) := by
    positivity
  calc
    ‖actualWordJointCutoff r
      (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff locations f‖ ≤
      (((Fintype.card (WilsonBoxPlaquettes N) : ℝ) * a ^ 4 * K) ^ r) *
        SchwartzMap.seminorm ℂ 0 0 f := hraw
    _ ≤ (6 * K * R ^ 4) ^ r *
        SchwartzMap.seminorm ℂ 0 0 f :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hb0 hcoord _) (apply_nonneg _ _)

end YMUIC.Original30
