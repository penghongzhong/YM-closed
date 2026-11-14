import YMOriginal.Original30_AllVolumeJointSchwartz
import YMOriginal.Original30_FixedBoxJointHierarchy
import YMOriginal.Original34_OSII_ExternalInterface
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03
open MeasureTheory

/-- The actual expected joint r-point Wilson-word distribution.
The coefficients are expectations in one and the same probability law;
no independence or Gaussian assumption is built into the definition. -/
def actualExpectedWordJointDistribution
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config)
    (r N : ℕ) (a : ℝ)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ) :
    YMUIC.Original34.JointTest r →L[ℂ] ℂ :=
  ∑ tuple : Fin r → TrueSpatialPlaquettes N,
    (∫ ω : Config,
      ∏ j : Fin r,
        (((a ^ 4 : ℝ) : ℂ) *
          actualWilsonPolynomial (U ω (tuple j))
            (words (tuple j)) (coeff (tuple j))) ∂μ) •
      jointSchwartzEvalCLM r (actualJointLatticePosition a tuple)

@[simp] theorem actual_expected_word_joint_distribution_apply
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config)
    (r N : ℕ) (a : ℝ)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (f : YMUIC.Original34.JointTest r) :
    actualExpectedWordJointDistribution μ r N a U words coeff f =
      ∑ tuple : Fin r → TrueSpatialPlaquettes N,
        (∫ ω : Config,
          ∏ j : Fin r,
            (((a ^ 4 : ℝ) : ℂ) *
              actualWilsonPolynomial (U ω (tuple j))
                (words (tuple j)) (coeff (tuple j))) ∂μ) *
          f (actualJointLatticePosition a tuple) := by
  simp [actualExpectedWordJointDistribution]

/-- Actual all-volume expected Wilson hierarchy. -/
def actualExpectedWordAllVolumeHierarchy
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config)
    (N : ℕ) (a : ℝ)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ) :
    YMUIC.Original34.SchwingerHierarchy where
  S r := actualExpectedWordJointDistribution μ r N a U words coeff

/-- The expected joint Wilson distribution has a cutoff/volume-uniform
Schwartz bound.  Measurability is required only for the actual finite
tuple coefficients whose expectations define the distribution. -/
theorem actual_expected_word_joint_all_volume_bound
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config) [IsProbabilityMeasure μ]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (hMeas : ∀ tuple : Fin r → TrueSpatialPlaquettes N,
      AEStronglyMeasurable
        (fun ω : Config =>
          ∏ j : Fin r,
            (((a ^ 4 : ℝ) : ℂ) *
              actualWilsonPolynomial (U ω (tuple j))
                (words (tuple j)) (coeff (tuple j)))) μ)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualExpectedWordJointDistribution μ r N a U words coeff f‖ ≤
      (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  let P : ℝ := SchwartzMap.seminorm ℂ 0 0 f +
    SchwartzMap.seminorm ℂ (8 * r) 0 f
  let weight := fun p : TrueSpatialPlaquettes N =>
    latticeFourDimWeight a p.2
  have hw (p : TrueSpatialPlaquettes N) : 0 ≤ weight p := by
    dsimp [weight, latticeFourDimWeight]
    exact Finset.prod_nonneg
      (fun i hi => lattice_one_dim_weight_nonneg a ha.le _)
  have hpoint (tuple : Fin r → TrueSpatialPlaquettes N) :
      (a ^ 4) ^ r * ‖f (actualJointLatticePosition a tuple)‖ ≤
        256 ^ r * P * (∏ j, weight (tuple j)) := by
    let D := ∏ j : Fin r, ∏ i : Fin 4,
      (1 + a * ((tuple j).2 i : ℝ)) ^ 2
    have hD : 0 < D := by dsimp [D]; positivity
    have hf :
        (1 + ‖actualJointLatticePosition a tuple‖ ^ (8 * r)) *
          ‖f (actualJointLatticePosition a tuple)‖ ≤ P := by
      have h0 := f.norm_le_seminorm ℂ (actualJointLatticePosition a tuple)
      have hq := f.norm_pow_mul_le_seminorm ℂ (8 * r)
        (actualJointLatticePosition a tuple)
      dsimp [P]
      nlinarith
    have hd := actual_joint_denominator_bound a ha.le tuple
    have hmul :
        ‖f (actualJointLatticePosition a tuple)‖ * D ≤
          256 ^ r * P := by
      calc
        _ ≤ (256 ^ r *
            (1 + ‖actualJointLatticePosition a tuple‖ ^ (8 * r))) *
            ‖f (actualJointLatticePosition a tuple)‖ := by
              simpa only [mul_comm] using
                mul_le_mul_of_nonneg_right hd
                  (norm_nonneg (f (actualJointLatticePosition a tuple)))
        _ ≤ 256 ^ r * P := by
          nlinarith [mul_le_mul_of_nonneg_left hf
            (by positivity : (0 : ℝ) ≤ 256 ^ r)]
    have hweight :
        (∏ j, weight (tuple j)) = (a ^ 4) ^ r / D := by
      simp only [weight, true_site_cubature_weight_identity,
        Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, D]
    rw [hweight]
    have hdiv := (le_div_iff₀ hD).mpr hmul
    calc
      _ ≤ (a ^ 4) ^ r * (256 ^ r * P / D) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have hcoeff (tuple : Fin r → TrueSpatialPlaquettes N) :
      ‖∫ ω : Config,
        ∏ j : Fin r,
          (((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial (U ω (tuple j))
              (words (tuple j)) (coeff (tuple j))) ∂μ‖ ≤
        ((a ^ 4) * K) ^ r := by
    let M : ℝ := ((a ^ 4) * K) ^ r
    have hM : 0 ≤ M := by
      dsimp [M]
      positivity
    have htuple (ω : Config) :
        ‖∏ j : Fin r,
          (((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial (U ω (tuple j))
              (words (tuple j)) (coeff (tuple j)))‖ ≤ M := by
      calc
        _ = ∏ j : Fin r,
            ((a ^ 4) *
              ‖actualWilsonPolynomial (U ω (tuple j))
                (words (tuple j)) (coeff (tuple j))‖) := by
          simp only [norm_prod, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha.le 4)]
        _ ≤ ∏ _j : Fin r, ((a ^ 4) * K) := by
          exact Finset.prod_le_prod₀
            (fun j hj => by positivity)
            (fun j hj =>
              mul_le_mul_of_nonneg_left
                ((actual_wilson_polynomial_bound
                  (U ω (tuple j)) (words (tuple j)) (coeff (tuple j))).trans
                  (hbudget (tuple j)))
                (pow_nonneg ha.le 4))
        _ = M := by
          dsimp [M]
          simp
    have hint : Integrable
        (fun ω : Config =>
          ∏ j : Fin r,
            (((a ^ 4 : ℝ) : ℂ) *
              actualWilsonPolynomial (U ω (tuple j))
                (words (tuple j)) (coeff (tuple j)))) μ :=
      Integrable.of_bound (hMeas tuple) M
        (Filter.Eventually.of_forall htuple)
    have hmean := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall htuple)
    simpa only [show μ.real Set.univ = 1 by simp, mul_one, M] using hmean
  have hterm (tuple : Fin r → TrueSpatialPlaquettes N) :
      ‖(∫ ω : Config,
        ∏ j : Fin r,
          (((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial (U ω (tuple j))
              (words (tuple j)) (coeff (tuple j))) ∂μ) *
          f (actualJointLatticePosition a tuple)‖ ≤
      (256 * K) ^ r * P * (∏ j, weight (tuple j)) := by
    rw [norm_mul]
    have hc := hcoeff tuple
    have hp := hpoint tuple
    have hfn : 0 ≤ ‖f (actualJointLatticePosition a tuple)‖ :=
      norm_nonneg _
    calc
      _ ≤ (((a ^ 4) * K) ^ r) *
          ‖f (actualJointLatticePosition a tuple)‖ :=
        mul_le_mul_of_nonneg_right hc hfn
      _ = K ^ r *
          ((a ^ 4) ^ r *
            ‖f (actualJointLatticePosition a tuple)‖) := by
        rw [mul_pow]
        ring
      _ ≤ K ^ r * (256 ^ r * P * (∏ j, weight (tuple j))) :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg hK _)
      _ = (256 * K) ^ r * P * (∏ j, weight (tuple j)) := by
        rw [mul_pow]
        ring
  have hsum :
      (∑ tuple : Fin r → TrueSpatialPlaquettes N,
        ∏ j : Fin r, weight (tuple j)) ≤ (96 : ℝ) ^ r := by
    rw [← Fintype.prod_sum]
    calc
      _ ≤ ∏ _j : Fin r, (96 : ℝ) :=
        Finset.prod_le_prod₀
          (fun j hj => Finset.sum_nonneg (fun p hp => hw p))
          (fun j hj =>
            lattice_plaquette_four_dimensional_uniform a ha ha1 N)
      _ = _ := by simp
  rw [actual_expected_word_joint_distribution_apply]
  calc
    ‖∑ tuple : Fin r → TrueSpatialPlaquettes N,
      (∫ ω : Config,
        ∏ j : Fin r,
          (((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial (U ω (tuple j))
              (words (tuple j)) (coeff (tuple j))) ∂μ) *
        f (actualJointLatticePosition a tuple)‖ ≤
      ∑ tuple : Fin r → TrueSpatialPlaquettes N,
        ‖(∫ ω : Config,
          ∏ j : Fin r,
            (((a ^ 4 : ℝ) : ℂ) *
              actualWilsonPolynomial (U ω (tuple j))
                (words (tuple j)) (coeff (tuple j))) ∂μ) *
          f (actualJointLatticePosition a tuple)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ tuple : Fin r → TrueSpatialPlaquettes N,
        (256 * K) ^ r * P * (∏ j, weight (tuple j)) :=
      Finset.sum_le_sum (fun tuple ht => hterm tuple)
    _ = (256 * K) ^ r * P *
        (∑ tuple : Fin r → TrueSpatialPlaquettes N,
          ∏ j, weight (tuple j)) := by rw [Finset.mul_sum]
    _ ≤ (256 * K) ^ r * P * 96 ^ r :=
      mul_le_mul_of_nonneg_left hsum (by dsimp [P]; positivity)
    _ = (24576 * K) ^ r * P := by
      rw [show (256 : ℝ) * 96 = 24576 by norm_num, ← mul_pow]
      ring
    _ = (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := rfl

/-- The actual expected finite-cutoff Wilson hierarchy satisfies the literal
OS75 E0' condition uniformly in the UV cutoff and spatial volume whenever
the finite Wilson-template budget K is uniform. -/
theorem actual_expected_word_all_volume_OS_E0prime
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config) [IsProbabilityMeasure μ]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (hMeas : ∀ (r : ℕ) (tuple : Fin r → TrueSpatialPlaquettes N),
      AEStronglyMeasurable
        (fun ω : Config =>
          ∏ j : Fin r,
            (((a ^ 4 : ℝ) : ℂ) *
              actualWilsonPolynomial (U ω (tuple j))
                (words (tuple j)) (coeff (tuple j)))) μ) :
    YMUIC.Original34.OS_E0prime
      (actualExpectedWordAllVolumeHierarchy μ N a U words coeff) := by
  let C : ℝ := 1 + 24576 * K
  have hBase : 0 ≤ 24576 * K := mul_nonneg (by norm_num) hK
  have hC : 0 < C := by dsimp [C]; linarith
  have hLe : 24576 * K ≤ C := by dsimp [C]; linarith
  refine ⟨8, 0, 1, C, (by norm_num), hC, ?_⟩
  intro r f
  have hraw := actual_expected_word_joint_all_volume_bound
    μ r N a ha ha1 U words coeff K hK hbudget (hMeas r) f
  have hpow : (24576 * K) ^ r ≤ C ^ r :=
    pow_le_pow_left₀ hBase hLe r
  have hP : 0 ≤ SchwartzMap.seminorm ℂ 0 0 f +
      SchwartzMap.seminorm ℂ (8 * r) 0 f := by positivity
  have hcontrol :
      SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f =
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f := by
    simp [YMUIC.OSTensor.jointSchwartzControl]
  have hfac : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
    exact_mod_cast Nat.one_le_factorial r
  change
    ‖actualExpectedWordJointDistribution μ r N a U words coeff f‖ ≤
      (1 * C ^ r * (Nat.factorial r : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f
  calc
    _ ≤ (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := hraw
    _ ≤ C ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) :=
      mul_le_mul_of_nonneg_right hpow hP
    _ = C ^ r *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f := by
      rw [hcontrol]
    _ ≤ (1 * C ^ r * (Nat.factorial r : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f := by
      have hctrl : 0 ≤
          YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f :=
        apply_nonneg _ _
      have hCr : 0 ≤ C ^ r := pow_nonneg hC.le _
      nlinarith [mul_le_mul_of_nonneg_right hfac
        (mul_nonneg hCr hctrl)]

#print axioms actual_expected_word_all_volume_OS_E0prime

end YMUIC.Original30
