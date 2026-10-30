import YMOriginal.Original30_AllVolumeBareHierarchy

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# OS II (1975), Sec IV.1: distribution order grows linearly in r

This is an analytically meaningful source-side strengthening of the
older formal OS_E0prime interface. The latter fixed the spatial weight
order q while growing only derivative order k*r; the published
condition E0' in Eq. (4.1) uses a Schwartz norm of order s*r in
R^(4r). We retain the earlier theorem, and prove a NEW separate
linear-order certificate, instead of weakening any old statement.

On actual SU2 BARE Wilson sources, we can take s=8 and obtain
all-volume and cutoff independence. No actual RG a^-d source,
physical continuum limits, positivity or mass gap is implied.
-/

/-- A strict, explicit all-order joint Schwartz E0'-shaped
linear-seminorm-order bound. This is not itself an OS reconstruction
theorem; the physical E1--E4 inputs and published result are separate. -/
def jointOS1975LinearOrderGrowth
    (H : YMUIC.Original34.SchwingerHierarchy) : Prop :=
  ∃ (s : ℕ) (A C : ℝ), 0 ≤ A ∧ 0 < C ∧
    ∀ (r : ℕ) (f : YMUIC.Original34.JointTest r),
      ‖H.S r f‖ ≤
        (A * C ^ r * (Nat.factorial r : ℝ)) *
          YMUIC.OSTensor.jointSchwartzControl r (s * r) (s * r) f

/-- The real bare Wilson hierarchy passes a linear-in-r
Schwartz spatial-weight AND derivative-order test. The regulator
and volume do not enter A,C,s. This statement uses full JOINT
4r-variable tests, not finite collections of factorized pure tests. -/
theorem actual_bare_wilson_joint_OS1975_growth
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    jointOS1975LinearOrderGrowth
      (actualSpatialBareSchwingerHierarchy N a U words coeff) := by
  let C : ℝ := 1 + 24576 * K
  have hC : 0 < C := by dsimp [C]; linarith
  have hbase : 0 ≤ 24576 * K := by positivity
  have hmono : 24576 * K ≤ C := by dsimp [C]; linarith
  refine ⟨8, 2, C, (by norm_num), hC, ?_⟩
  intro r f
  let J : ℝ := YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f
  have hJ : 0 ≤ J := apply_nonneg _ _
  have hp := ((YMUIC.OSTensor.joint_schwartz_control r (8 * r) (8 * r)).2
    f 0 (by omega))
  have hsem :
      SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ (8 * r) 0 f ≤ 2 * J := by
    dsimp [J]
    linarith [hp.1, hp.2]
  have hbound := actual_joint_bare_wilson_all_volume_canonical
    r N a ha ha1 U words coeff K hK hbudget f
  have hpow : (24576 * K) ^ r ≤ C ^ r :=
    pow_le_pow_left₀ hbase hmono r
  have hCpow : 0 ≤ C ^ r := pow_nonneg hC.le _
  have hfct : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
    have hn : 1 ≤ Nat.factorial r := by
      have hx := Nat.factorial_pos r
      omega
    exact_mod_cast hn
  have hcoefficient :
      (24576 * K) ^ r * 2 ≤
        2 * C ^ r * (Nat.factorial r : ℝ) := by
    calc
      _ ≤ C ^ r * 2 :=
        mul_le_mul_of_nonneg_right hpow (by norm_num)
      _ ≤ (C ^ r * 2) * (Nat.factorial r : ℝ) := by
        have ht : 0 ≤ C ^ r * 2 := by positivity
        nlinarith
      _ = 2 * C ^ r * (Nat.factorial r : ℝ) := by ring
  change ‖(actualSpatialBareSchwingerHierarchy N a U words coeff).S r f‖ ≤
    (2 * C ^ r * (Nat.factorial r : ℝ)) * J
  calc
    _ = ‖actualWordJointCutoff r
      (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (actualJointSpatialLocation r N a) f‖ := by
        exact congrArg norm (actual_word_joint_distribution_apply
          r (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
            U words coeff (actualJointSpatialLocation r N a) f)
    _ ≤ (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := hbound
    _ ≤ (24576 * K) ^ r * (2 * J) :=
      mul_le_mul_of_nonneg_left hsem (pow_nonneg hbase _)
    _ = ((24576 * K) ^ r * 2) * J := by ring
    _ ≤ (2 * C ^ r * (Nat.factorial r : ℝ)) * J :=
      mul_le_mul_of_nonneg_right hcoefficient hJ

end YMUIC.Original30
