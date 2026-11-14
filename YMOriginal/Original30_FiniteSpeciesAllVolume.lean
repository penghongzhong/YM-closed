import YMOriginal.Original30_VolumeUniformWilsonSchwartz
import YMOriginal.Original30_JointLatticeSchwartz
import YMOriginal.Original34_OSII_ExternalInterface
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- A fixed finite family of physical source species at every true 4D site. -/
abbrev TrueSpatialSources (S : Type*) (N : ℕ) :=
  S × (Fin 4 → Fin N)

/-- Concatenated physical positions for arbitrary fixed finite source species. -/
def actualJointSpeciesPosition
    {S : Type*} {r N : ℕ} (a : ℝ)
    (tuple : Fin r → TrueSpatialSources S N) :
    EuclideanSpace ℝ (Fin (4 * r)) :=
  WithLp.toLp 2 (fun k => a *
    ((tuple ⟨k.val / 4, by have := k.isLt; omega⟩).2
      ⟨k.val % 4, by omega⟩ : ℝ))

theorem actual_joint_species_coordinate_le_norm
    {S : Type*} {r N : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (tuple : Fin r → TrueSpatialSources S N)
    (j : Fin r) (i : Fin 4) :
    a * ((tuple j).2 i : ℝ) ≤ ‖actualJointSpeciesPosition a tuple‖ := by
  let k : Fin (4 * r) :=
    ⟨4 * j.val + i.val, by
      have hj := j.isLt
      have hi := i.isLt
      omega⟩
  have hk : (actualJointSpeciesPosition a tuple) k =
      a * ((tuple j).2 i : ℝ) := by
    have hd : (4 * j.val + i.val) / 4 = j.val := by omega
    have hm : (4 * j.val + i.val) % 4 = i.val := by omega
    simp [actualJointSpeciesPosition, k, hd, hm]
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have h := Finset.single_le_sum
    (fun l (_ : l ∈ (Finset.univ : Finset (Fin (4 * r)))) =>
      sq_nonneg ((actualJointSpeciesPosition a tuple) l))
    (Finset.mem_univ k)
  simpa only [hk] using h

theorem actual_joint_species_denominator_bound
    {S : Type*} {r N : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (tuple : Fin r → TrueSpatialSources S N) :
    (∏ j : Fin r, ∏ i : Fin 4,
      (1 + a * ((tuple j).2 i : ℝ)) ^ 2) ≤
      256 ^ r *
        (1 + ‖actualJointSpeciesPosition a tuple‖ ^ (8 * r)) := by
  let t : ℝ := ‖actualJointSpeciesPosition a tuple‖
  have hp :
      (∏ j : Fin r, ∏ i : Fin 4,
        (1 + a * ((tuple j).2 i : ℝ)) ^ 2) ≤
      ∏ _j : Fin r, ∏ _i : Fin 4, (1 + t) ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro j hj
      positivity
    intro j hj
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    intro i hi
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add_right
        (actual_joint_species_coordinate_le_norm a ha tuple j i) 1) 2
  have htwo : (2 : ℝ) ^ (8 * r - 1) ≤ 2 ^ (8 * r) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  calc
    _ ≤ ∏ _j : Fin r, ∏ _i : Fin 4, (1 + t) ^ 2 := hp
    _ = (1 + t) ^ (8 * r) := by
      simp only [Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← pow_mul]
    _ ≤ 2 ^ (8 * r - 1) * (1 + t ^ (8 * r)) := by
      simpa only [one_pow] using
        add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
          (norm_nonneg _) (8 * r)
    _ ≤ 2 ^ (8 * r) * (1 + t ^ (8 * r)) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = 256 ^ r * (1 + t ^ (8 * r)) := by
      rw [pow_mul]
      norm_num

/-- Fixed finite species multiply the 4D lattice cubature only by their
cardinality; no physical-volume factor occurs. -/
theorem finite_species_lattice_weight_uniform
    {S : Type*} [Fintype S]
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    (∑ p : TrueSpatialSources S N,
      latticeFourDimWeight a p.2) ≤
      (Fintype.card S : ℝ) * 16 := by
  have h4 := lattice_four_dimensional_uniform_all_cutoffs a ha ha1 N
  calc
    (∑ p : TrueSpatialSources S N,
      latticeFourDimWeight a p.2) =
      ∑ _s : S, ∑ site : Fin 4 → Fin N,
        latticeFourDimWeight a site := by
          simp only [Fintype.sum_prod_type]
    _ = (Fintype.card S : ℝ) *
        (∑ site : Fin 4 → Fin N,
          latticeFourDimWeight a site) := by
      simp
    _ ≤ (Fintype.card S : ℝ) * 16 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)

/-- Genuine joint 4r-variable all-volume bound for ANY fixed finite
source species family.  For six species this reduces to the earlier
24576*K constant; for the D=4 Gram source take S=RootFiber21. -/
theorem actual_word_joint_finite_species_all_volume_bound
    {S W T : Type*} [Fintype S] [Fintype T]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialSources S N → W → SU2)
    (words : TrueSpatialSources S N → T → List (List W))
    (coeff : TrueSpatialSources S N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualWordJointCutoff r
      (fun _ : TrueSpatialSources S N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (actualJointSpeciesPosition a) f‖ ≤
      (4096 * (Fintype.card S : ℝ) * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  let P := SchwartzMap.seminorm ℂ 0 0 f +
    SchwartzMap.seminorm ℂ (8 * r) 0 f
  let weight := fun p : TrueSpatialSources S N =>
    latticeFourDimWeight a p.2
  have hw (p : TrueSpatialSources S N) : 0 ≤ weight p := by
    dsimp [weight, latticeFourDimWeight]
    exact Finset.prod_nonneg
      (fun i hi => lattice_one_dim_weight_nonneg a ha.le _)
  have hpoint (tuple : Fin r → TrueSpatialSources S N) :
      (a ^ 4) ^ r * ‖f (actualJointSpeciesPosition a tuple)‖ ≤
        256 ^ r * P * (∏ j, weight (tuple j)) := by
    let D := ∏ j : Fin r, ∏ i : Fin 4,
      (1 + a * ((tuple j).2 i : ℝ)) ^ 2
    have hD : 0 < D := by dsimp [D]; positivity
    have hf :
        (1 + ‖actualJointSpeciesPosition a tuple‖ ^ (8 * r)) *
          ‖f (actualJointSpeciesPosition a tuple)‖ ≤ P := by
      have h0 := f.norm_le_seminorm ℂ (actualJointSpeciesPosition a tuple)
      have hq := f.norm_pow_mul_le_seminorm ℂ (8 * r)
        (actualJointSpeciesPosition a tuple)
      dsimp [P]
      nlinarith
    have hd := actual_joint_species_denominator_bound a ha.le tuple
    have hmul :
        ‖f (actualJointSpeciesPosition a tuple)‖ * D ≤
          256 ^ r * P := by
      calc
        _ ≤ (256 ^ r *
            (1 + ‖actualJointSpeciesPosition a tuple‖ ^ (8 * r))) *
            ‖f (actualJointSpeciesPosition a tuple)‖ := by
              simpa only [mul_comm] using
                mul_le_mul_of_nonneg_right hd
                  (norm_nonneg (f (actualJointSpeciesPosition a tuple)))
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
  have hterm (tuple : Fin r → TrueSpatialSources S N) :
      ‖(∏ j : Fin r,
          ((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial
              (U (tuple j)) (words (tuple j)) (coeff (tuple j))) *
          f (actualJointSpeciesPosition a tuple)‖ ≤
      (256 * K) ^ r * P * (∏ j, weight (tuple j)) := by
    have ho :
        (∏ j : Fin r,
          ‖actualWilsonPolynomial
            (U (tuple j)) (words (tuple j)) (coeff (tuple j))‖) ≤
          K ^ r := by
      calc
        _ ≤ ∏ _j : Fin r, K :=
          Finset.prod_le_prod₀
            (fun j hj => norm_nonneg _)
            (fun j hj =>
              (actual_wilson_polynomial_bound
                (U (tuple j)) (words (tuple j)) (coeff (tuple j))).trans
                (hbudget (tuple j)))
        _ = _ := by simp
    have h :=
      mul_le_mul_of_nonneg_right ho
        (mul_nonneg (by positivity : 0 ≤ (a ^ 4) ^ r)
          (norm_nonneg (f (actualJointSpeciesPosition a tuple))))
    have hh :=
      mul_le_mul_of_nonneg_left (hpoint tuple) (pow_nonneg hK r)
    simp only [norm_mul, norm_prod, norm_pow,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha.le, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ = (∏ j : Fin r,
          ‖actualWilsonPolynomial
            (U (tuple j)) (words (tuple j)) (coeff (tuple j))‖) *
          ((a ^ 4) ^ r *
            ‖f (actualJointSpeciesPosition a tuple)‖) := by ring
      _ ≤ K ^ r *
          ((a ^ 4) ^ r *
            ‖f (actualJointSpeciesPosition a tuple)‖) := h
      _ ≤ K ^ r *
          (256 ^ r * P * (∏ j, weight (tuple j))) := hh
      _ = (256 * K) ^ r * P * (∏ j, weight (tuple j)) := by
        rw [mul_pow]
        ring
  have hsum :
      (∑ tuple : Fin r → TrueSpatialSources S N,
        ∏ j : Fin r, weight (tuple j)) ≤
      (((Fintype.card S : ℝ) * 16) ^ r) := by
    rw [← Fintype.prod_sum]
    calc
      _ ≤ ∏ _j : Fin r, ((Fintype.card S : ℝ) * 16) :=
        Finset.prod_le_prod₀
          (fun j hj => Finset.sum_nonneg (fun p hp => hw p))
          (fun j hj => finite_species_lattice_weight_uniform a ha ha1 N)
      _ = _ := by simp
  calc
    _ ≤ ∑ tuple : Fin r → TrueSpatialSources S N,
      ‖(∏ j : Fin r,
          ((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial
              (U (tuple j)) (words (tuple j)) (coeff (tuple j))) *
        f (actualJointSpeciesPosition a tuple)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ tuple : Fin r → TrueSpatialSources S N,
        (256 * K) ^ r * P * (∏ j, weight (tuple j)) :=
      Finset.sum_le_sum (fun tuple ht => hterm tuple)
    _ = (256 * K) ^ r * P *
        (∑ tuple : Fin r → TrueSpatialSources S N,
          ∏ j, weight (tuple j)) := by rw [Finset.mul_sum]
    _ ≤ (256 * K) ^ r * P *
        (((Fintype.card S : ℝ) * 16) ^ r) :=
      mul_le_mul_of_nonneg_left hsum (by dsimp [P]; positivity)
    _ = (4096 * (Fintype.card S : ℝ) * K) ^ r * P := by
      rw [← mul_pow]
      congr 2
      ring
    _ = (4096 * (Fintype.card S : ℝ) * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := rfl

end YMUIC.Original30
