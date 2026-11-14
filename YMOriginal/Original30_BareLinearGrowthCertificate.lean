import YMOriginal.Original30_AllVolumeJointSchwartz
import YM.OSTensor.JointSchwartzControl
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-!
A linear-in-order weighted joint Schwartz certificate for the existing
BARE Wilson lattice moments. This is not the published OS norm dictionary,
the renormalized source, a continuum limit, or an Original30 acceptance.
-/

theorem bare_joint_linear_weight_factorial_bound
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
      (2 * Real.exp (24576 * K)) * (r.factorial : ℝ) *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f := by
  obtain ⟨hint, hbound⟩ := actual_word_joint_probability_all_volume
    μ r N a ha ha1 U words coeff K hK hbudget f hMeas
  refine ⟨hint, ?_⟩
  let P : ℝ := YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f
  have hp : 0 ≤ P := apply_nonneg _ _
  have hcontrol := (YMUIC.OSTensor.joint_schwartz_control r (8 * r) (8 * r)).2 f 0 (by omega)
  have hsum : SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f ≤ 2 * P := by
    dsimp [P]
    linarith [hcontrol.1, hcontrol.2]
  have hfactorial : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hexp : (24576 * K) ^ r ≤ Real.exp (24576 * K) * (r.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (24576 * K) (by positivity) r
    exact (div_le_iff₀ hfactorial).mp h
  calc
    _ ≤ (24576 * K) ^ r *
      (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f) := hbound
    _ ≤ (24576 * K) ^ r * (2 * P) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (Real.exp (24576 * K) * (r.factorial : ℝ)) * (2 * P) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := by dsimp [P]; ring

#print axioms bare_joint_linear_weight_factorial_bound

end YMUIC.Original30
