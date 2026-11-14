import YMOriginal.Original42_BookendCertificate
import YMOriginal.Original42_B14VanishingDefect

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.Original42

open YMUIC.ConditionalI7
open YMUIC.Original34

/-!
# A DISTINCT continuum-only U-I-C terminal certificate

Original42UICMain is NOT modified. It requires a uniform gap for
EVERY cutoff generator as well as the continuum generator.
That stronger historical 39/39 CONDITIONAL theorem still uses I7.

This file states only the properties needed of the CONTINUUM theory.
Its gap conclusion is obtained from B14 with a cutoff error tending
to zero along the same joint cutoff-volume filter. It does not
assume a positive regulator gap or original I7.

The model-side approximate Gram contraction is visible and OPEN for
actual 4D SU2 Wilson measure, so this is not an unconditional Clay
Yang--Mills theorem.
-/

/-- Continuum U-I-C conclusion: same phase/local/OS/nontriviality
stages, but no demand that every finite regulator itself be gapped. -/
def Original42ContinuumOnlyMain
    {Hcont : Type*} [NormedAddCommGroup Hcont]
    [InnerProductSpace ℂ Hcont] [CompleteSpace Hcont]
    (OmegaCont : Hcont)
    (Acont : vacuumSector OmegaCont →ₗ.[ℂ] vacuumSector OmegaCont)
    (S : Original42Stages) (gap : ℝ) : Prop :=
  S.phaseLocked ∧
  S.jointCutoffVolumeLimits ∧
  S.fixedDLocalPolynomialBlock ∧
  S.rotationMatchingO4 ∧
  S.continuumReflectionPositivity ∧
  S.continuumOSGrowth ∧
  S.continuumNontriviality ∧
  S.osWightmanReconstruction ∧
  0 < gap ∧
  ((gap : ℝ) : EReal) ≤ generatorGap Acont

/-- Distinct continuum-only terminal result without an I7 premise.
The SAME Schwinger hierarchy produces all OS-side stages, while
the CONTINUUM generator gap follows from same-net asymptotic
Gram contraction. The physical source inequality hcut is openly
an unproved model obligation rather than a renamed mass-gap axiom. -/
theorem original42_continuum_only_from_asymptotic_gram
    {Rot PosPoly Cut J Hcont : Type*}
    {l : Filter Cut} [l.NeBot]
    [NormedAddCommGroup Hcont]
    [InnerProductSpace ℂ Hcont] [CompleteSpace Hcont]
    (Phase Joint Local Nontrivial : Prop)
    (Gtest : OSTestGeometry Rot PosPoly)
    (PublishedOS : PublishedOSII Gtest)
    (Hsch : SchwingerHierarchy)
    (hOS : Original34ManuscriptInputs Gtest Hsch)
    (hPhase : Phase)
    (hJoint : Joint)
    (hLocal : Local)
    (hNontrivial : Nontrivial)
    (OmegaCont : Hcont)
    (v : J → vacuumSector OmegaCont)
    (Tcont : vacuumSector OmegaCont →L[ℂ] vacuumSector OmegaCont)
    (Acont : vacuumSector OmegaCont →ₗ.[ℂ] vacuumSector OmegaCont)
    (t d : ℝ) (ht : 0 < t) (hd : 0 < d)
    (hcalc : NonnegativeHeatCalculus Acont t Tcont)
    (hdense : Dense (Submodule.span ℂ (Set.range v) :
      Set (vacuumSector OmegaCont)))
    (Q0 Qt : Cut → Finset J → (J → ℂ) → ℝ)
    (hQ0lim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Q0 k s c) l
        (𝓝 (‖∑ j ∈ s, c j • v j‖ ^ 2)))
    (hQtlim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Qt k s c) l
        (𝓝 (⟪Tcont (∑ j ∈ s, c j • v j),
              ∑ j ∈ s, c j • v j⟫_ℂ).re))
    (err : Cut → ℝ)
    (cost : Finset J → (J → ℂ) → ℝ)
    (herr0 : Tendsto err l (𝓝 0))
    (hcut : ∀ (s : Finset J) (c : J → ℂ),
      ∀ᶠ k in l, Qt k s c ≤ Real.exp (-t * d) * Q0 k s c +
        err k * cost s c) :
    Original42ContinuumOnlyMain OmegaCont Acont
      (stagesFromOSHierarchy Phase Joint Local Nontrivial
        Gtest PublishedOS Hsch) d := by
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
  have hGap : ((d : ℝ) : EReal) ≤ generatorGap Acont :=
    b14_continuum_gap_from_vanishing_cutoff_defect
      v Tcont Acont t d ht hd hcalc hdense
      Q0 Qt hQ0lim hQtlim err cost herr0 hcut
  exact ⟨hPhase, hJoint, hLocal, hRotation, hRP,
    hGrowth, hNontrivial, hReconstruction, hd, hGap⟩

#print axioms original42_continuum_only_from_asymptotic_gram

end YMUIC.Original42
