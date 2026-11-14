import YMOriginal.Original30_AllVolumeJointSchwartz
import YMOriginal.Original30_FixedBoxJointHierarchy
import YMOriginal.Original34_OSII_ExternalInterface

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- The actual all-volume finite-cutoff Wilson-word hierarchy, now using the
true 4r-dimensional lattice position rather than a fixed physical box. -/
def actualWordAllVolumeHierarchy
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ) :
    YMUIC.Original34.SchwingerHierarchy where
  S r := actualWordJointDistribution r
    (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U words coeff (actualJointLatticePosition a)

/-- The genuine all-volume joint Wilson hierarchy satisfies the literal OS75
E0' linear-growth condition uniformly in the number of lattice sites.
This is still the bounded bare Wilson-word hierarchy; identifying the
renormalized D=4 source cocycle with it is a separate model dictionary. -/
theorem actual_word_all_volume_OS_E0prime
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    YMUIC.Original34.OS_E0prime
      (actualWordAllVolumeHierarchy N a U words coeff) := by
  let C : ℝ := 1 + 24576 * K
  have hBase : 0 ≤ 24576 * K := mul_nonneg (by norm_num) hK
  have hC : 0 < C := by
    dsimp [C]
    linarith
  have hLe : 24576 * K ≤ C := by
    dsimp [C]
    linarith
  refine ⟨8, 0, 1, C, (by norm_num), hC, ?_⟩
  intro r f
  have hraw :=
    actual_word_joint_all_volume_bound
      r N a ha ha1 U words coeff K hK hbudget f
  have hpow : (24576 * K) ^ r ≤ C ^ r :=
    pow_le_pow_left₀ hBase hLe r
  have hP : 0 ≤
      SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ (8 * r) 0 f := by
    positivity
  have hcontrol :
      SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f =
        YMUIC.OSTensor.jointSchwartzControl
          r (8 * r) (0 * r) f := by
    simp [YMUIC.OSTensor.jointSchwartzControl]
  have hfac : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
    exact_mod_cast Nat.one_le_factorial r
  change
    ‖actualWordJointDistribution r
      (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (actualJointLatticePosition a) f‖ ≤
      (1 * C ^ r * (Nat.factorial r : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f
  calc
    ‖actualWordJointDistribution r
      (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (actualJointLatticePosition a) f‖ =
      ‖actualWordJointCutoff r
        (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
        U words coeff (actualJointLatticePosition a) f‖ := by
          rw [actual_word_joint_distribution_apply]
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

#print axioms actual_word_all_volume_OS_E0prime

end YMUIC.Original30
