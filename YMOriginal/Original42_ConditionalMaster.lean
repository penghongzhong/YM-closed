import YMConditional.Original16_FromI7

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.Original42
open YMUIC.ConditionalI7

/-!
# Original manuscript ID 42, C29 Theorem 21.1: conditional U-I-C assembly

This is the actual *conditional* final theorem, not an unconditional
Yang-Mills mass-gap assertion. I7 is a visible premise, and the quantitative
mass-gap term is derived from the already officially compiled ORIGINAL 16,
rather than passed as a goal-sized new axiom or merely named a conclusion.

The other manuscript hypotheses (phase lock, same joint limit, local
polynomials, O(4) matching, continuum RP/growth, nontriviality and
OS/Wightman reconstruction) are visible and remain conditional. Their
underlying physical Yang-Mills producers are NOT proved by this assembly.
-/

/-- The seven manuscript premises of C29 Theorem 21.1, except for the
actual I7-based semigroup-gap data, which are displayed separately
in the exact Hilbert-space arguments of the theorem below. -/
structure Original42Stages where
  phaseLocked : Prop
  jointCutoffVolumeLimits : Prop
  fixedDLocalPolynomialBlock : Prop
  rotationMatchingO4 : Prop
  continuumReflectionPositivity : Prop
  continuumOSGrowth : Prop
  continuumNontriviality : Prop
  osWightmanReconstruction : Prop

/-- Explicit conditional U-I-C conclusion: retains every U/C item and
requires an ACTUAL, uniformly positive lower bound on the full generator
spectrum on each vacuum-orthogonal Hilbert sector. -/
def Original42UICMain
    {κ : Type*} (V : κ → Type*)
    [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)]
    [∀ k, CompleteSpace (V k)]
    (Ω : ∀ k, V k)
    (A : ∀ k, vacuumSector (Ω k) →ₗ.[ℂ] vacuumSector (Ω k))
    {H∞ : Type*} [NormedAddCommGroup H∞]
    [InnerProductSpace ℂ H∞] [CompleteSpace H∞]
    (Ω∞ : H∞) (A∞ : vacuumSector Ω∞ →ₗ.[ℂ] vacuumSector Ω∞)
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
  (∀ k, ((gap : ℝ) : EReal) ≤ generatorGap (A k)) ∧
  ((gap : ℝ) : EReal) ≤ generatorGap A∞

/-- Original #42 conditional master theorem, preserving the original
seven listed input classes and the previously verified Original #16
I7->uniform spectral gap proof.  I7 is NOT proved here.

No eigenvector assumption, no identification of different cutoff Hilbert
spaces and no spectral gap assertion is passed as a theorem parameter.
The only spectral-calculus hypothesis is exactly the previously audited
NonnegativeHeatCalculus interface used by Original #16. -/
theorem original42_master_assembly_from_I7
    {κ : Type*}
    (V : κ → Type*) (I : Type*)
    [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)]
    [∀ k, CompleteSpace (V k)]
    (Ω : ∀ k, V k) (v : ∀ k, I → V k)
    (T : ∀ k, V k →L[ℂ] V k)
    (η cPlus Lambda : ℝ) (a : κ → ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hc : 0 < cPlus) (hLambda : 0 < Lambda)
    (ha : ∀ k, 0 < a k)
    (hT : ∀ k, (T k).IsPositive)
    (hfix : ∀ k, T k (Ω k) = Ω k)
    (hdense : ∀ k,
      Dense (Submodule.span ℂ (Set.range (v k)) : Set (V k)))
    (hI7 : ∀ k, I7Gram
      (fun i => center (Ω k) (v k i)) (T k) η)
    (A : ∀ k, vacuumSector (Ω k) →ₗ.[ℂ] vacuumSector (Ω k))
    (hSpectral : ∀ k, NonnegativeHeatCalculus (A k) (2 * a k)
      (vacuumTransfer (Ω k) (T k) (hT k).isSelfAdjoint (hfix k)))
    (hscale : ∀ k, a k ≤ cPlus / Lambda)
    {H∞ : Type*} [NormedAddCommGroup H∞]
    [InnerProductSpace ℂ H∞] [CompleteSpace H∞]
    (Ω∞ : H∞) (A∞ : vacuumSector Ω∞ →ₗ.[ℂ] vacuumSector Ω∞)
    (hB14 : ∀ d : ℝ,
      (∀ k, ((d : ℝ) : EReal) ≤ generatorGap (A k)) →
        ((d : ℝ) : EReal) ≤ generatorGap A∞)
    (S : Original42Stages)
    (hPhase : S.phaseLocked)
    (hJoint : S.jointCutoffVolumeLimits)
    (hLocal : S.fixedDLocalPolynomialBlock)
    (hRotation : S.rotationMatchingO4)
    (hRP : S.continuumReflectionPositivity)
    (hGrowth : S.continuumOSGrowth)
    (hNontrivial : S.continuumNontriviality)
    (hReconstruction : S.osWightmanReconstruction) :
    Original42UICMain V Ω A Ω∞ A∞ S
      ((-Real.log (1 - η) / (2 * cPlus)) * Lambda) := by
  have hGap := original16_uniform_mass_gap_from_I7
    V I Ω v T η cPlus Lambda a
    hη0 hη1 hc hLambda ha hT hfix hdense hI7
    A hSpectral hscale
  exact ⟨hPhase, hJoint, hLocal, hRotation, hRP,
    hGrowth, hNontrivial, hReconstruction, hGap.1, hGap.2,
    hB14 _ hGap.2⟩

#print axioms original42_master_assembly_from_I7

end YMUIC.Original42
