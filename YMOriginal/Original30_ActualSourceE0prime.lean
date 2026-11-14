import YMOriginal.Original30_SourceJointUniformBound
import YMOriginal.Original34_OSII_ExternalInterface

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- The genuine finite-cutoff Schwinger hierarchy built from the actual
Wilson exponential-source derivatives on general joint 4r-variable
Schwartz tests. -/
def actualWilsonSourceHierarchy
    {Ω W T : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype T]
    (μ : MeasureTheory.Measure Ω)
    (N : ℕ) (a : ℝ)
    (U : Ω → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ) :
    YMUIC.Original34.SchwingerHierarchy where
  S r := actualWilsonSourceJointDistribution μ
    (fun _ => ((a ^ 4 : ℝ) : ℂ))
    U words coeff r (actualJointLatticePosition a)

/-- The actual finite-cutoff Wilson source hierarchy satisfies the literal
OS75 E0' joint-Schwartz growth under one cutoff-uniform finite-template
budget.  This is a theorem about the source-derivative hierarchy itself,
not about a surrogate bare moment family. -/
theorem actual_wilson_source_hierarchy_OS_E0prime
    {Ω W T : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype T]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Ω → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (hU : ∀ p w, Continuous (fun ω => U ω p w))
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    YMUIC.Original34.OS_E0prime
      (actualWilsonSourceHierarchy μ N a U words coeff) := by
  refine ⟨8, 8, 2 * Real.exp (24576 * K), 1, ?_, by norm_num, ?_⟩
  · positivity
  · intro r f
    have h := actual_source_joint_uniform_bound
      μ r N a ha ha1 U words coeff hU K hK hbudget f
    simpa [actualWilsonSourceHierarchy] using h

/-- Uniform literal OS75 E0' bounds pass to any pointwise joint-Schwartz
continuum limit.  This is the exact functional-analytic bridge needed after
v116/v118 have produced the SAME joint hierarchy limit. -/
theorem OS_E0prime_of_uniform_joint_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (Hcut : ι → YMUIC.Original34.SchwingerHierarchy)
    (H : YMUIC.Original34.SchwingerHierarchy)
    (q k : ℕ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 < C)
    (hbound : ∀ i r (f : YMUIC.Original34.JointTest r),
      ‖(Hcut i).S r f‖ ≤
        (A * C ^ r * (Nat.factorial r : ℝ)) *
          YMUIC.OSTensor.jointSchwartzControl r (q * r) (k * r) f)
    (hlim : ∀ r (f : YMUIC.Original34.JointTest r),
      Tendsto (fun i => (Hcut i).S r f) l (𝓝 (H.S r f))) :
    YMUIC.Original34.OS_E0prime H := by
  refine ⟨q, k, A, C, hA, hC, ?_⟩
  intro r f
  have hnorm :
      Tendsto (fun i => ‖(Hcut i).S r f‖) l (𝓝 ‖H.S r f‖) :=
    (continuous_norm.tendsto _).comp (hlim r f)
  exact le_of_tendsto hnorm
    (Filter.Eventually.of_forall (fun i => hbound i r f))

#print axioms actual_wilson_source_hierarchy_OS_E0prime
#print axioms OS_E0prime_of_uniform_joint_limit

end YMUIC.Original30
