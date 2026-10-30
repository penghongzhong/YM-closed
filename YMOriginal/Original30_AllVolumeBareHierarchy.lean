import YMOriginal.Original30_CanonicalJointLocations
import YMOriginal.Original30_FixedBoxJointHierarchy

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# Actual all-volume SU(2) bare Wilson Schwinger hierarchy

The fixed-box joint Schwartz distributions are now constructed at
the TRUE 4r canonical physical locations, and the all-volume joint
Schwartz estimate gives one continuous distribution at every r.

This file carefully states only linear-in-r spatial-weight Schwartz
growth, using p_(8r,0).  It does NOT identify that growth with the
previously registered stronger fixed-weight Original34.OS_E0prime,
nor prove actual a^-d RG-normalized YM Schwinger continuum limits.
-/

/-- True finite-regulator family of continuous joint Schwartz
distributions, sharing the same actual SU2 Wilson configuration. -/
def actualSpatialBareSchwingerHierarchy
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ) :
    YMUIC.Original34.SchwingerHierarchy where
  S r := actualWordJointDistribution r
    (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U words coeff (actualJointSpatialLocation r N a)

/-- Transparent joint-test growth criterion with spatial weight and
derivative order both allowed to grow at most linearly in r.
This is distinct from and weaker than Original34.OS_E0prime. -/
def jointLinearWeightGrowth
    (H : YMUIC.Original34.SchwingerHierarchy) : Prop :=
  ∃ (q k : ℕ) (A C : ℝ), 0 ≤ A ∧ 0 < C ∧
    ∀ (r : ℕ) (f : YMUIC.Original34.JointTest r),
      ‖H.S r f‖ ≤
        (A * C ^ r * (Nat.factorial r : ℝ)) *
          YMUIC.OSTensor.jointSchwartzControl r (q * r) (k * r) f

/-- The true a^4-weighted, all-volume, all-r SU(2) Wilson hierarchy
has linear-weight single-factorial joint Schwartz growth without
assuming an analytic source chart or a pure tensor factorization. -/
theorem actual_spatial_bare_hierarchy_linear_weight_growth
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    jointLinearWeightGrowth
      (actualSpatialBareSchwingerHierarchy N a U words coeff) := by
  let C : ℝ := 1 + 24576 * K
  have hC : 0 < C := by
    dsimp [C]
    linarith
  have hbase : 0 ≤ 24576 * K := by positivity
  have hmono : 24576 * K ≤ C := by
    dsimp [C]
    linarith
  refine ⟨8, 0, 1, C, (by norm_num), hC, ?_⟩
  intro r f
  have hbound := actual_joint_bare_wilson_all_volume_canonical
      r N a ha ha1 U words coeff K hK hbudget f
  have hcontrol :
      YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f =
        SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f := by
    simp [YMUIC.OSTensor.jointSchwartzControl]
  have hcontrol0 :
      0 ≤ YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f :=
    apply_nonneg _ _
  have hpow : (24576 * K) ^ r ≤ C ^ r :=
    pow_le_pow_left₀ hbase hmono r
  have hfac : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
    have h := Nat.factorial_pos r
    exact_mod_cast (show 1 ≤ Nat.factorial r by omega)
  have hCpow : 0 ≤ C ^ r := pow_nonneg hC.le r
  have hfactor : C ^ r ≤ 1 * C ^ r * (Nat.factorial r : ℝ) := by
    calc
      C ^ r = C ^ r * 1 := by ring
      _ ≤ C ^ r * (Nat.factorial r : ℝ) :=
        mul_le_mul_of_nonneg_left hfac hCpow
      _ = 1 * C ^ r * (Nat.factorial r : ℝ) := by ring
  calc
    ‖(actualSpatialBareSchwingerHierarchy N a U words coeff).S r f‖ =
        ‖actualWordJointCutoff r
          (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
          U words coeff (actualJointSpatialLocation r N a) f‖ := by
      exact congrArg norm (actual_word_joint_distribution_apply
        r (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
          U words coeff (actualJointSpatialLocation r N a) f)
    _ ≤ (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := hbound
    _ ≤ C ^ r *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f := by
      rw [hcontrol]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (1 * C ^ r * (Nat.factorial r : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (0 * r) f :=
      mul_le_mul_of_nonneg_right hfactor hcontrol0

end YMUIC.Original30
