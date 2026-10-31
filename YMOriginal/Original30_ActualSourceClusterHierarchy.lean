import YMOriginal.Original30_JointUltrafilterCompactness
import YMOriginal.Original30_SourceJointUniformBound

set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- The actual finite Wilson source distributions, with regulator-dependent
configuration spaces, probability laws, lattice sizes and coefficients, have
a normalized common cluster hierarchy on ALL joint Schwartz tests. The same
ultrafilter works for every order and refines the given regulator filter.
The coefficient budget K is uniform by hypothesis. No convergence of moments
is assumed. This does not prove physical renormalized coefficient control,
uniqueness across ultrafilters, or convergence along the original filter. -/
theorem actual_source_cluster_hierarchy
    {ι : Type*} (l : Filter ι) [NeBot l]
    {Ω W : ι → Type*} {T : Type*} [Fintype T]
    [∀ i, TopologicalSpace (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, OpensMeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (N : ι → ℕ) (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (U : ∀ i, Ω i → TrueSpatialPlaquettes (N i) → W i → SU2)
    (words : ∀ i, TrueSpatialPlaquettes (N i) → T → List (List (W i)))
    (coeff : ∀ i, TrueSpatialPlaquettes (N i) → T → ℂ)
    (hU : ∀ i p w, Continuous (fun ω => U i ω p w))
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ i p, actualWilsonPolynomialBudget (words i p) (coeff i p) ≤ K) :
    ∃ u : Ultrafilter ι, (u : Filter ι) ≤ l ∧
      ∃! H : YMUIC.Original34.SchwingerHierarchy,
        (∀ r f, Tendsto (fun i =>
          actualWilsonSourceJointDistribution (μ i) (fun _ => ((a i ^ 4 : ℝ) : ℂ))
            (U i) (words i) (coeff i) r (actualJointLatticePosition (a i)) f)
          (u : Filter ι) (𝓝 (H.S r f))) ∧
        (∀ f : YMUIC.Original34.JointTest 0, H.S 0 f = f 0) ∧
        ∀ r f, ‖H.S r f‖ ≤
          (2 * Real.exp (24576 * K)) * (r.factorial : ℝ) *
            YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f := by
  let L (r : ℕ) (i : ι) : YMUIC.Original34.JointTest r →L[ℂ] ℂ :=
    actualWilsonSourceJointDistribution (μ i) (fun _ => ((a i ^ 4 : ℝ) : ℂ))
      (U i) (words i) (coeff i) r (actualJointLatticePosition (a i))
  let C (r : ℕ) : ℝ := (2 * Real.exp (24576 * K)) * (r.factorial : ℝ)
  have hb (r : ℕ) (i : ι) (f : YMUIC.Original34.JointTest r) :
      ‖L r i f‖ ≤ C r * YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f :=
    actual_source_joint_uniform_bound (μ i) r (N i) (a i) (ha i) (ha1 i)
      (U i) (words i) (coeff i) (hU i) K hK (hbudget i) f
  obtain ⟨u, hul, H, hH, huniq⟩ :=
    joint_ultrafilter_compactness l L (fun r => 8 * r) (fun r => 8 * r) C hb
  have hzero (i : ι) (f : YMUIC.Original34.JointTest 0) : L 0 i f = f 0 := by
    rw [(actual_wilson_joint_source_dictionary (μ i)
      (fun _ => ((a i ^ 4 : ℝ) : ℂ)) (U i) (words i) (coeff i) (hU i)
      0 (actualJointLatticePosition (a i)) f).2]
    have hpos (tuple : Fin 0 → TrueSpatialPlaquettes (N i)) :
        actualJointLatticePosition (a i) tuple = 0 := by
      ext k
      have := k.isLt
      omega
    simp [actualWordJointCutoff, hpos]
  refine ⟨u, hul, H, ⟨hH.1, ?_, hH.2⟩, ?_⟩
  · intro f
    apply tendsto_nhds_unique (hH.1 0 f)
    simpa only [hzero] using (tendsto_const_nhds (x := f 0) (f := (u : Filter ι)))
  · intro H' hH'
    exact huniq H' ⟨hH'.1, hH'.2.2⟩

end YMUIC.Original30
