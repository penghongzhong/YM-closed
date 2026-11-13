import YMOriginal.Original30_VolumeUniformWilsonSchwartz
import YMOriginal.Original30_JointLatticeSchwartz
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- The actual concatenated positions of all r lattice plaquettes. -/
def actualJointLatticePosition {r N : ℕ} (a : ℝ)
    (tuple : Fin r → TrueSpatialPlaquettes N) :
    EuclideanSpace ℝ (Fin (4 * r)) :=
  WithLp.toLp 2 (fun k => a *
    ((tuple ⟨k.val / 4, by have := k.isLt; omega⟩).2
      ⟨k.val % 4, by omega⟩ : ℝ))

theorem actual_joint_coordinate_le_norm {r N : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (tuple : Fin r → TrueSpatialPlaquettes N) (j : Fin r) (i : Fin 4) :
    a * ((tuple j).2 i : ℝ) ≤ ‖actualJointLatticePosition a tuple‖ := by
  let k : Fin (4 * r) := ⟨4 * j.val + i.val, by have := j.isLt; have := i.isLt; omega⟩
  have hk : (actualJointLatticePosition a tuple) k =
      a * ((tuple j).2 i : ℝ) := by
    have hd : (4 * j.val + i.val) / 4 = j.val := by omega
    have hm : (4 * j.val + i.val) % 4 = i.val := by omega
    simp [actualJointLatticePosition, k, hd, hm]
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have h := Finset.single_le_sum
    (fun l (_ : l ∈ (Finset.univ : Finset (Fin (4 * r)))) =>
      sq_nonneg ((actualJointLatticePosition a tuple) l)) (Finset.mem_univ k)
  simpa only [hk] using h

/-- Polynomial weight loss linear in the order, with exponential constants. -/
theorem actual_joint_denominator_bound {r N : ℕ}
    (a : ℝ) (ha : 0 ≤ a) (tuple : Fin r → TrueSpatialPlaquettes N) :
    (∏ j : Fin r, ∏ i : Fin 4, (1 + a * ((tuple j).2 i : ℝ)) ^ 2) ≤
      256 ^ r * (1 + ‖actualJointLatticePosition a tuple‖ ^ (8 * r)) := by
  let t : ℝ := ‖actualJointLatticePosition a tuple‖
  have hp : (∏ j : Fin r, ∏ i : Fin 4,
      (1 + a * ((tuple j).2 i : ℝ)) ^ 2) ≤
      ∏ _j : Fin r, ∏ _i : Fin 4, (1 + t) ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro j hj; positivity
    intro j hj
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    intro i hi
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add_right (actual_joint_coordinate_le_norm a ha tuple j i) 1) 2
  have htwo : (2 : ℝ) ^ (8 * r - 1) ≤ 2 ^ (8 * r) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  calc
    _ ≤ ∏ _j : Fin r, ∏ _i : Fin 4, (1 + t) ^ 2 := hp
    _ = (1 + t) ^ (8 * r) := by simp only [Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ 2 ^ (8 * r - 1) * (1 + t ^ (8 * r)) := by
      simpa only [one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
        (norm_nonneg _) (8 * r)
    _ ≤ 2 ^ (8 * r) * (1 + t ^ (8 * r)) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = 256 ^ r * (1 + t ^ (8 * r)) := by rw [pow_mul]; norm_num

/-- A genuine joint test, no tensor factorization, no finite box radius.
This is a bare Wilson estimate; it does not supply renormalized source matching. -/
theorem actual_word_joint_all_volume_bound
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (actualJointLatticePosition a) f‖ ≤
      (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  let P := SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f
  let weight := fun p : TrueSpatialPlaquettes N => latticeFourDimWeight a p.2
  have hw (p) : 0 ≤ weight p := by
    dsimp [weight, latticeFourDimWeight]
    exact Finset.prod_nonneg (fun i hi => lattice_one_dim_weight_nonneg a ha.le _)
  have hpoint (tuple : Fin r → TrueSpatialPlaquettes N) :
      (a ^ 4) ^ r * ‖f (actualJointLatticePosition a tuple)‖ ≤
        256 ^ r * P * (∏ j, weight (tuple j)) := by
    let D := ∏ j : Fin r, ∏ i : Fin 4, (1 + a * ((tuple j).2 i : ℝ)) ^ 2
    have hD : 0 < D := by dsimp [D]; positivity
    have hf : (1 + ‖actualJointLatticePosition a tuple‖ ^ (8 * r)) *
        ‖f (actualJointLatticePosition a tuple)‖ ≤ P := by
      have h0 := f.norm_le_seminorm ℂ (actualJointLatticePosition a tuple)
      have hq := f.norm_pow_mul_le_seminorm ℂ (8 * r) (actualJointLatticePosition a tuple)
      dsimp [P]
      nlinarith
    have hd := actual_joint_denominator_bound a ha.le tuple
    have hmul : ‖f (actualJointLatticePosition a tuple)‖ * D ≤ 256 ^ r * P := by
      calc
        _ ≤ (256 ^ r * (1 + ‖actualJointLatticePosition a tuple‖ ^ (8 * r))) *
          ‖f (actualJointLatticePosition a tuple)‖ := by
            simpa only [mul_comm] using mul_le_mul_of_nonneg_right hd
              (norm_nonneg (f (actualJointLatticePosition a tuple)))
        _ ≤ 256 ^ r * P := by nlinarith [mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤ 256 ^ r)]
    have hweight : (∏ j, weight (tuple j)) = (a ^ 4) ^ r / D := by
      simp only [weight, true_site_cubature_weight_identity, Finset.prod_div_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, D]
    rw [hweight]
    have hdiv := (le_div_iff₀ hD).mpr hmul
    calc
      _ ≤ (a ^ 4) ^ r * (256 ^ r * P / D) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have hterm (tuple : Fin r → TrueSpatialPlaquettes N) :
      ‖(∏ j : Fin r, ((a ^ 4 : ℝ) : ℂ) *
        actualWilsonPolynomial (U (tuple j)) (words (tuple j)) (coeff (tuple j))) *
        f (actualJointLatticePosition a tuple)‖ ≤
      (256 * K) ^ r * P * (∏ j, weight (tuple j)) := by
    have ho : (∏ j : Fin r,
        ‖actualWilsonPolynomial (U (tuple j)) (words (tuple j)) (coeff (tuple j))‖) ≤ K ^ r := by
      calc
        _ ≤ ∏ _j : Fin r, K := Finset.prod_le_prod₀
          (fun j hj => norm_nonneg _) (fun j hj =>
            (actual_wilson_polynomial_bound _ _ _).trans (hbudget _))
        _ = _ := by simp
    have h := mul_le_mul_of_nonneg_right ho
      (mul_nonneg (by positivity : 0 ≤ (a ^ 4) ^ r)
        (norm_nonneg (f (actualJointLatticePosition a tuple))))
    have hh := mul_le_mul_of_nonneg_left (hpoint tuple) (pow_nonneg hK r)
    simp only [norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha.le, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ = (∏ j : Fin r, ‖actualWilsonPolynomial (U (tuple j))
        (words (tuple j)) (coeff (tuple j))‖) *
        ((a ^ 4) ^ r * ‖f (actualJointLatticePosition a tuple)‖) := by ring
      _ ≤ K ^ r * ((a ^ 4) ^ r * ‖f (actualJointLatticePosition a tuple)‖) := h
      _ ≤ K ^ r * (256 ^ r * P * (∏ j, weight (tuple j))) := hh
      _ = _ := by rw [mul_pow]; ring
  have hsum : (∑ tuple : Fin r → TrueSpatialPlaquettes N,
      ∏ j : Fin r, weight (tuple j)) ≤ (96 : ℝ) ^ r := by
    rw [← Fintype.prod_sum]
    calc
      _ ≤ ∏ _j : Fin r, (96 : ℝ) := Finset.prod_le_prod₀
        (fun j hj => Finset.sum_nonneg (fun p hp => hw p))
        (fun j hj => lattice_plaquette_four_dimensional_uniform a ha ha1 N)
      _ = _ := by simp
  calc
    _ ≤ ∑ tuple : Fin r → TrueSpatialPlaquettes N,
      ‖(∏ j : Fin r, ((a ^ 4 : ℝ) : ℂ) *
        actualWilsonPolynomial (U (tuple j)) (words (tuple j)) (coeff (tuple j))) *
        f (actualJointLatticePosition a tuple)‖ := norm_sum_le _ _
    _ ≤ ∑ tuple : Fin r → TrueSpatialPlaquettes N,
      (256 * K) ^ r * P * (∏ j, weight (tuple j)) :=
        Finset.sum_le_sum (fun tuple ht => hterm tuple)
    _ = (256 * K) ^ r * P *
      (∑ tuple : Fin r → TrueSpatialPlaquettes N, ∏ j, weight (tuple j)) := by rw [Finset.mul_sum]
    _ ≤ (256 * K) ^ r * P * 96 ^ r :=
      mul_le_mul_of_nonneg_left hsum (by dsimp [P]; positivity)
    _ = ((256 * K) * 96) ^ r * P := by simp only [mul_pow]; ring
    _ = (24576 * K) ^ r * P := by rw [show (256 * K) * 96 = 24576 * K by ring]

/-- The same estimate for the genuine joint moment of any probability law.
No independence, factorized test, cubature bound or moment bound is assumed. -/
theorem actual_word_joint_probability_all_volume
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : MeasureTheory.Measure Config) [MeasureTheory.IsProbabilityMeasure μ]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r)
    (hMeas : MeasureTheory.AEStronglyMeasurable
      (fun ω => actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f) μ) :
    MeasureTheory.Integrable
      (fun ω => actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f) μ ∧
    ‖∫ ω, actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
      (U ω) words coeff (actualJointLatticePosition a) f ∂μ‖ ≤
      (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  let M := (24576 * K) ^ r *
    (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f)
  have hbound (ω : Config) :
      ‖actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f‖ ≤ M :=
    actual_word_joint_all_volume_bound r N a ha ha1 (U ω) words coeff K hK hbudget f
  refine ⟨MeasureTheory.Integrable.of_bound hMeas M
    (Filter.Eventually.of_forall hbound), ?_⟩
  have hmean := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall hbound)
  simpa only [show μ.real Set.univ = 1 by simp, mul_one] using hmean

end YMUIC.Original30
