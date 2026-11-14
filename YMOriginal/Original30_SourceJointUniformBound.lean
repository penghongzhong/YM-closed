import YMOriginal.Original30_JointSourceDictionary
import YMOriginal.Original30_BareLinearGrowthCertificate

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- The distribution constructed from actual source derivatives inherits
cutoff/volume uniform factorial growth. Measurability is derived from the
source dictionary. The coefficient budget K is still an explicit input;
its uniformity for physically renormalized coefficients is not proved. -/
theorem actual_source_joint_uniform_bound
    {Ω W T : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [Fintype T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Ω → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (hU : ∀ p w, Continuous (fun ω => U ω p w))
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualWilsonSourceJointDistribution μ (fun _ => ((a ^ 4 : ℝ) : ℂ))
      U words coeff r (actualJointLatticePosition a) f‖ ≤
      (2 * Real.exp (24576 * K)) * (r.factorial : ℝ) *
        YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f := by
  obtain ⟨hint, heq⟩ := actual_wilson_joint_source_dictionary μ
    (fun _ => ((a ^ 4 : ℝ) : ℂ)) U words coeff hU r (actualJointLatticePosition a) f
  rw [heq]
  exact (bare_joint_linear_weight_factorial_bound μ r N a ha ha1 U words coeff
    K hK hbudget f hint.aestronglyMeasurable).2

end YMUIC.Original30
