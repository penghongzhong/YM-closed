import YMOriginal.Original30_FiniteSpeciesAllVolume
import YMOriginal.Original30_FixedBoxJointHierarchy
import YMOriginal.Original34_OSII_ExternalInterface
import YM.Wilson.CandidateGramRoots21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson YMUICV128.Section03

/-- Joint D=4 source distribution for an arbitrary fixed finite family
of bounded local observables.  The physical a^4 measure factor is explicit. -/
def actualBoundedSpeciesJointDistribution
    {S : Type*} [Fintype S]
    (r N : ℕ) (a : ℝ)
    (O : TrueSpatialSources S N → ℂ) :
    YMUIC.Original34.JointTest r →L[ℂ] ℂ :=
  ∑ tuple : Fin r → TrueSpatialSources S N,
    (∏ j : Fin r, (((a ^ 4 : ℝ) : ℂ) * O (tuple j))) •
      jointSchwartzEvalCLM r (actualJointSpeciesPosition a tuple)

@[simp] theorem actual_bounded_species_joint_distribution_apply
    {S : Type*} [Fintype S]
    (r N : ℕ) (a : ℝ)
    (O : TrueSpatialSources S N → ℂ)
    (f : YMUIC.Original34.JointTest r) :
    actualBoundedSpeciesJointDistribution r N a O f =
      ∑ tuple : Fin r → TrueSpatialSources S N,
        (∏ j : Fin r, (((a ^ 4 : ℝ) : ℂ) * O (tuple j))) *
          f (actualJointSpeciesPosition a tuple) := by
  simp [actualBoundedSpeciesJointDistribution]

/-- All-volume joint Schwartz bound for any fixed finite D=4 source family
whose local observables are uniformly bounded by K.  No RG source cocycle,
analytic source radius, or fixed physical box enters the estimate. -/
theorem actual_bounded_species_joint_all_volume_bound
    {S : Type*} [Fintype S]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (O : TrueSpatialSources S N → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hO : ∀ p, ‖O p‖ ≤ K)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualBoundedSpeciesJointDistribution r N a O f‖ ≤
      (4096 * (Fintype.card S : ℝ) * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  let P : ℝ := SchwartzMap.seminorm ℂ 0 0 f +
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
      ‖(∏ j : Fin r, (((a ^ 4 : ℝ) : ℂ) * O (tuple j))) *
          f (actualJointSpeciesPosition a tuple)‖ ≤
      (256 * K) ^ r * P * (∏ j, weight (tuple j)) := by
    have hprodO :
        (∏ j : Fin r, ‖O (tuple j)‖) ≤ K ^ r := by
      calc
        _ ≤ ∏ _j : Fin r, K :=
          Finset.prod_le_prod₀
            (fun j hj => norm_nonneg _)
            (fun j hj => hO (tuple j))
        _ = K ^ r := by simp
    have hmult :=
      mul_le_mul_of_nonneg_right hprodO
        (mul_nonneg (by positivity : 0 ≤ (a ^ 4) ^ r)
          (norm_nonneg (f (actualJointSpeciesPosition a tuple))))
    have hgeom :=
      mul_le_mul_of_nonneg_left (hpoint tuple) (pow_nonneg hK r)
    simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ha.le 4), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ = (∏ j : Fin r, ‖O (tuple j)‖) *
          ((a ^ 4) ^ r *
            ‖f (actualJointSpeciesPosition a tuple)‖) := by ring
      _ ≤ K ^ r *
          ((a ^ 4) ^ r *
            ‖f (actualJointSpeciesPosition a tuple)‖) := hmult
      _ ≤ K ^ r *
          (256 ^ r * P * (∏ j, weight (tuple j))) := hgeom
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
  rw [actual_bounded_species_joint_distribution_apply]
  calc
    ‖∑ tuple : Fin r → TrueSpatialSources S N,
        (∏ j : Fin r, (((a ^ 4 : ℝ) : ℂ) * O (tuple j))) *
          f (actualJointSpeciesPosition a tuple)‖ ≤
      ∑ tuple : Fin r → TrueSpatialSources S N,
        ‖(∏ j : Fin r, (((a ^ 4 : ℝ) : ℂ) * O (tuple j))) *
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

/-- Hierarchy generated by one bounded local D=4 observable family. -/
def actualBoundedSpeciesHierarchy
    {S : Type*} [Fintype S]
    (N : ℕ) (a : ℝ)
    (O : TrueSpatialSources S N → ℂ) :
    YMUIC.Original34.SchwingerHierarchy where
  S r := actualBoundedSpeciesJointDistribution r N a O

/-- Literal OS75 E0' for every fixed finite bounded D=4 source family. -/
theorem actual_bounded_species_OS_E0prime
    {S : Type*} [Fintype S]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (O : TrueSpatialSources S N → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hO : ∀ p, ‖O p‖ ≤ K) :
    YMUIC.Original34.OS_E0prime
      (actualBoundedSpeciesHierarchy N a O) := by
  let C : ℝ := 1 + 4096 * (Fintype.card S : ℝ) * K
  have hBase : 0 ≤ 4096 * (Fintype.card S : ℝ) * K := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hLe : 4096 * (Fintype.card S : ℝ) * K ≤ C := by
    dsimp [C]
    linarith
  refine ⟨8, 0, 1, C, (by norm_num), hC, ?_⟩
  intro r f
  have hraw :=
    actual_bounded_species_joint_all_volume_bound
      r N a ha ha1 O K hK hO f
  have hpow :
      (4096 * (Fintype.card S : ℝ) * K) ^ r ≤ C ^ r :=
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
  change ‖actualBoundedSpeciesJointDistribution r N a O f‖ ≤
    (1 * C ^ r * (Nat.factorial r : ℝ)) *
      YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f
  calc
    _ ≤ (4096 * (Fintype.card S : ℝ) * K) ^ r *
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

/-- Actual 21-component SU(2) Gram-root observable at one lattice site. -/
def actualCandidateGramObservable21
    {N : ℕ}
    (U : (Fin 4 → Fin N) → GramPlaquette6 → SU2)
    (p : TrueSpatialSources RootFiber21 N) : ℂ :=
  (candidateGramRoot21 (U p.2) p.1 : ℂ)

theorem actual_candidate_gram_observable21_bound
    {N : ℕ}
    (U : (Fin 4 → Fin N) → GramPlaquette6 → SU2)
    (p : TrueSpatialSources RootFiber21 N) :
    ‖actualCandidateGramObservable21 U p‖ ≤ 4 := by
  rw [actualCandidateGramObservable21, Complex.norm_real, Real.norm_eq_abs]
  exact candidate_gram_root21_abs_le_four (U p.2) p.1

/-- D=4 21-root hierarchy has cutoff- and volume-uniform literal OS75 E0'
without any cumulative source-cocycle norm. -/
theorem actual_candidate_gram21_OS_E0prime
    {N : ℕ}
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : (Fin 4 → Fin N) → GramPlaquette6 → SU2) :
    YMUIC.Original34.OS_E0prime
      (actualBoundedSpeciesHierarchy N a
        (actualCandidateGramObservable21 U)) :=
  actual_bounded_species_OS_E0prime
    N a ha ha1 (actualCandidateGramObservable21 U)
      4 (by norm_num) (actual_candidate_gram_observable21_bound U)

#print axioms actual_candidate_gram21_OS_E0prime

end YMUIC.Original30
