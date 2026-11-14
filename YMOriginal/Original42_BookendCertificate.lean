import YMOriginal.Original42_ConditionalMaster
import YMOriginal.Original34_ManuscriptReconstruction

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.Original42
open YMUIC.ConditionalI7
open YMUIC.Original34

/-!
# I7-assumed U-I-C bookend certificate

This file performs only final wiring. It does not add a Yang--Mills
estimate or hide I7.

The same continuum Schwinger hierarchy H supplies E0'--E4 through
Original34ManuscriptInputs. Hence rotation covariance, continuum
reflection positivity, factorial growth, and OS/Wightman reconstruction
are no longer four unrelated propositions passed by hand to Original42.

The four genuinely model-side stage outputs that remain visible are:
phase lock, the joint cutoff-volume limit, the fixed-D/all-D local
polynomial block, and continuum nontriviality. The continuum gap-passage
map is also explicit. Published Osterwalder--Seiler and OS-II inputs, and
I7 itself, remain visible premises.
-/

/-- Concrete Original42 stage record generated from one actual continuum
Schwinger hierarchy and its OS manuscript certificate. -/
def stagesFromOSHierarchy
    {Rot PosPoly : Type*}
    (Phase Joint Local Nontrivial : Prop)
    (G : OSTestGeometry Rot PosPoly)
    (Published : PublishedOSII G)
    (H : SchwingerHierarchy) : Original42Stages where
  phaseLocked := Phase
  jointCutoffVolumeLimits := Joint
  fixedDLocalPolynomialBlock := Local
  rotationMatchingO4 :=
    ∀ (r : ℕ) (R : Rot) (f : JointTest r),
      H.S r (G.rotate r R f) = H.S r f
  continuumReflectionPositivity :=
    ∀ p : PosPoly, G.positiveTime p →
      (G.reflectedPolynomialMoment H p p).im = 0 ∧
      0 ≤ (G.reflectedPolynomialMoment H p p).re
  continuumOSGrowth := OS_E0prime H
  continuumNontriviality := Nontrivial
  osWightmanReconstruction :=
    ∃ W : Published.WightmanTheory,
      Published.satisfies_R0prime_R5 W ∧
      Published.euclideanBoundaryOf W H ∧
      (∀ W' : Published.WightmanTheory,
        Published.satisfies_R0prime_R5 W' →
        Published.euclideanBoundaryOf W' H →
        Published.vacuumUnitaryEquivalent W W')

/-- Final modular bookend. All OS-side stage fields are produced from the
single Original34ManuscriptInputs certificate, and the mass gap is
produced from the explicit I7 hypothesis plus the published
Osterwalder--Seiler transfer input. -/
theorem original42_bookend_from_actual_OS_hierarchy_and_I7
    {Rot PosPoly κ : Type*}
    (Phase Joint Local Nontrivial : Prop)
    (Gtest : OSTestGeometry Rot PosPoly)
    (PublishedOS : PublishedOSII Gtest)
    (Hsch : SchwingerHierarchy)
    (hOS : Original34ManuscriptInputs Gtest Hsch)
    (hPhase : Phase)
    (hJoint : Joint)
    (hLocal : Local)
    (hNontrivial : Nontrivial)
    (V : κ → Type*) (I : Type*)
    [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)]
    [∀ k, CompleteSpace (V k)]
    (Ω : ∀ k, V k) (v : ∀ k, I → V k)
    (T : ∀ k, V k →L[ℂ] V k)
    (OS : YMUIC.Original15Published.PublishedOsterwalderSeilerTransfer V Ω T)
    (η cPlus Lambda : ℝ) (a : κ → ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hc : 0 < cPlus) (hLambda : 0 < Lambda)
    (ha : ∀ k, 0 < a k)
    (hdense : ∀ k,
      Dense (Submodule.span ℂ (Set.range (v k)) : Set (V k)))
    (hI7 : ∀ k, I7Gram
      (fun i => center (Ω k) (v k i)) (T k) η)
    (A : ∀ k, vacuumSector (Ω k) →ₗ.[ℂ] vacuumSector (Ω k))
    (hSpectral : ∀ k, NonnegativeHeatCalculus (A k) (2 * a k)
      (vacuumTransfer (Ω k) (T k) (OS.positive k).isSelfAdjoint
        (OS.vacuumFixed k)))
    (hscale : ∀ k, a k ≤ cPlus / Lambda)
    {Hcont : Type*} [NormedAddCommGroup Hcont]
    [InnerProductSpace ℂ Hcont] [CompleteSpace Hcont]
    (OmegaCont : Hcont)
    (Acont : vacuumSector OmegaCont →ₗ.[ℂ] vacuumSector OmegaCont)
    (hB14 : ∀ d : ℝ,
      (∀ k, ((d : ℝ) : EReal) ≤ generatorGap (A k)) →
        ((d : ℝ) : EReal) ≤ generatorGap Acont) :
    Original42UICMain V Ω A OmegaCont Acont
      (stagesFromOSHierarchy Phase Joint Local Nontrivial
        Gtest PublishedOS Hsch)
      ((-Real.log (1 - η) / (2 * cPlus)) * Lambda) := by
  let S := stagesFromOSHierarchy Phase Joint Local Nontrivial
    Gtest PublishedOS Hsch
  have hRotation : S.rotationMatchingO4 := by
    intro r R f
    exact hOS.fromOriginal31_E1_rotations r R f
  have hRP : S.continuumReflectionPositivity := by
    intro p hp
    exact hOS.fromOriginal28_E2 p hp
  have hGrowth : S.continuumOSGrowth :=
    hOS.fromOriginal30_E0prime
  have hReconstruction : S.osWightmanReconstruction :=
    original34_manuscript_reconstruction Gtest PublishedOS Hsch hOS
  exact original42_master_assembly_from_published_OS_and_I7
    V I Ω v T OS η cPlus Lambda a
    hη0 hη1 hc hLambda ha hdense hI7 A hSpectral hscale
    OmegaCont Acont hB14 S
    hPhase hJoint hLocal hRotation hRP hGrowth
    hNontrivial hReconstruction

#print axioms original42_bookend_from_actual_OS_hierarchy_and_I7

end YMUIC.Original42
