import YMOriginal.Original30_JointLatticeSchwartz
import Mathlib.Analysis.Distribution.TemperedDistribution

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# The finite-cutoff 4r-variable Wilson hierarchy as ACTUAL distributions

Each joint source is a genuine continuous linear functional on the
FULL 4r-dimensional Schwartz test space. Construct it by a finite sum
of Dirac delta evaluation maps with the actual a^4-weighted SU2
Wilson-word polynomial coefficients.

This is NOT merely an unstructured function f -> complex scalar.
It provides an actual continuous Schwinger functional of every order,
with a regulator-uniform factorial Schwartz bound for a FIXED physical
box R. The infinite-volume R->infinity limit and physical a^-d
renormalized YM source are NOT covered by this fixed-box theorem.
-/

/-- Continuous complex-linear evaluation of the entire JOINT Schwartz
test at an exact 4r-dimensional point. -/
def jointSchwartzEvalCLM (r : ℕ)
    (x : EuclideanSpace ℝ (Fin (4 * r))) :
    YMUIC.Original34.JointTest r →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ
      (EuclideanSpace ℝ (Fin (4 * r))) ℂ)

@[simp] theorem joint_schwartz_eval_clm_apply (r : ℕ)
    (x : EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r) :
    jointSchwartzEvalCLM r x f = f x := by
  simp [jointSchwartzEvalCLM]

/-- Construct the actual r-point finite-volume Wilson source as a
continuous linear Schwartz distribution, with no assumed continuity. -/
def actualWordJointDistribution
    {P W T : Type*} [Fintype P] [Fintype T]
    (r : ℕ) (weights : P → ℂ)
    (U : P → W → SU2)
    (words : P → T → List (List W))
    (coeff : P → T → ℂ)
    (locations : (Fin r → P) →
      EuclideanSpace ℝ (Fin (4 * r))) :
    YMUIC.Original34.JointTest r →L[ℂ] ℂ :=
  ∑ tuple : Fin r → P,
    (∏ j : Fin r,
      weights (tuple j) *
        actualWilsonPolynomial (U (tuple j))
          (words (tuple j)) (coeff (tuple j))) •
      jointSchwartzEvalCLM r (locations tuple)

/-- The constructed joint distribution acts exactly as the actual
finite-cutoff Wilson-word lattice source, not a new abstract model. -/
theorem actual_word_joint_distribution_apply
    {P W T : Type*} [Fintype P] [Fintype T]
    (r : ℕ) (weights : P → ℂ)
    (U : P → W → SU2)
    (words : P → T → List (List W))
    (coeff : P → T → ℂ)
    (locations : (Fin r → P) →
      EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r) :
    actualWordJointDistribution r weights U words coeff locations f =
      actualWordJointCutoff r weights U words coeff locations f := by
  simp [actualWordJointDistribution, actualWordJointCutoff]

/-- A genuine r-point continuous Schwinger hierarchy built at every
order from the SAME finite link/Wilson polynomial configuration,
without assuming a source analytic chart. -/
def actualWordPhysicalBoxHierarchy
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ)
    (U : WilsonBoxPlaquettes N → W → SU2)
    (words : WilsonBoxPlaquettes N → T → List (List W))
    (coeff : WilsonBoxPlaquettes N → T → ℂ)
    (locations : (r : ℕ) →
      (Fin r → WilsonBoxPlaquettes N) →
        EuclideanSpace ℝ (Fin (4 * r))) :
    YMUIC.Original34.SchwingerHierarchy where
  S r := actualWordJointDistribution r
    (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U words coeff (locations r)

/-- For every fixed finite physical box, the TRUE joint Schwartz
Schwinger hierarchy has the corrected factorial E0' bound without
postulating a uniform analytic source radius or assuming E0' as input.
The unrenormalized source normalization and R->infty are still open. -/
theorem actual_word_physical_box_OS_E0prime
    {W T : Type*} [Fintype T]
    (N : ℕ) (a R : ℝ)
    (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hbox : (N : ℝ) * a ≤ R)
    (U : WilsonBoxPlaquettes N → W → SU2)
    (words : WilsonBoxPlaquettes N → T → List (List W))
    (coeff : WilsonBoxPlaquettes N → T → ℂ)
    (locations : (r : ℕ) →
      (Fin r → WilsonBoxPlaquettes N) →
        EuclideanSpace ℝ (Fin (4 * r)))
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    YMUIC.Original34.OS_E0prime
      (actualWordPhysicalBoxHierarchy N a U words coeff locations) := by
  let C : ℝ := 1 + 6 * K * R ^ 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hBase : 0 ≤ 6 * K * R ^ 4 := by positivity
  have hLe : 6 * K * R ^ 4 ≤ C := by dsimp [C]; linarith
  refine ⟨0, 0, 1, C, (by norm_num), hC, ?_⟩
  intro r f
  have hbound :=
    actual_word_joint_physical_box_bound r N a R ha hR hbox
      U words coeff (locations r) f K hK hbudget
  have hcontrol :
      SchwartzMap.seminorm ℂ 0 0 f ≤
        YMUIC.OSTensor.jointSchwartzControl r 0 (0 * r) f :=
    ((YMUIC.OSTensor.joint_schwartz_control r 0 (0 * r)).2
      f 0 (by omega)).1
  have hp : 0 ≤
      YMUIC.OSTensor.jointSchwartzControl r 0 (0 * r) f :=
    apply_nonneg _ _
  have hfactorial : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
    have hn : 1 ≤ Nat.factorial r := by
      have hpos := Nat.factorial_pos r
      omega
    exact_mod_cast hn
  have hpow : (6 * K * R ^ 4) ^ r ≤ C ^ r :=
    pow_le_pow_left₀ hBase hLe r
  have hpowPos : 0 ≤ C ^ r := pow_nonneg hC.le r
  change ‖actualWordJointDistribution r
    (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U words coeff (locations r) f‖ ≤
    1 * C ^ r * (Nat.factorial r : ℝ) *
      YMUIC.OSTensor.jointSchwartzControl r 0 (0 * r) f
  calc
    ‖actualWordJointDistribution r
      (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (locations r) f‖ =
      ‖actualWordJointCutoff r
        (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
        U words coeff (locations r) f‖ := by
          rw [actual_word_joint_distribution_apply]
    _ ≤ (6 * K * R ^ 4) ^ r * SchwartzMap.seminorm ℂ 0 0 f :=
      hbound
    _ ≤ C ^ r * SchwartzMap.seminorm ℂ 0 0 f :=
      mul_le_mul_of_nonneg_right hpow (apply_nonneg _ _)
    _ ≤ C ^ r *
      YMUIC.OSTensor.jointSchwartzControl r 0 (0 * r) f :=
      mul_le_mul_of_nonneg_left hcontrol hpowPos
    _ ≤ 1 * C ^ r * (Nat.factorial r : ℝ) *
      YMUIC.OSTensor.jointSchwartzControl r 0 (0 * r) f := by
      have hmult : 0 ≤ C ^ r *
        YMUIC.OSTensor.jointSchwartzControl r 0 (0 * r) f :=
        mul_nonneg hpowPos hp
      have hf :=
        mul_le_mul_of_nonneg_right hfactorial hmult
      nlinarith

end YMUIC.Original30
