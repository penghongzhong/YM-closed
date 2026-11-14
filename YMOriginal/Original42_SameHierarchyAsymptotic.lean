import YMOriginal.Original42_ContinuumOnlyAsymptotic

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.Original42

open YMUIC.ConditionalI7
open YMUIC.Original34

/-!
# Actual same-Schwinger-hierarchy source-matched B14 terminal interface

The earlier abstract continuum-only bookend takes Gram limits Q0,Qt
as inputs, but its Schwinger hierarchy Hsch and its continuum
Hilbert representation could be unrelated.

This theorem FORCES the cutoff Gram forms to be pulled back from
the SAME actual family Hcut of Euclidean Schwinger hierarchies and
FORCES their limit to pair the SAME continuum Hsch with the OS
Hilbert realization v,Tcont.

The model source-to-Hilbert identities, convergence and the strict
asymptotic contraction remain explicit hypotheses; this is NOT a
physical 4D SU2 mass-gap proof. There is NO hI7 assumption.

Original42UICMain is untouched. This theorem targets ONLY the
separately named continuum-only conclusion.
-/

/-- A source-matched continuum-only conditional U-I-C bookend.
The *positive-time* source polynomials and their shifted versions
are explicitly from the same OS test geometry. -/
theorem original42_continuum_only_from_same_schwinger_gram
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
    (Hcut : Cut → SchwingerHierarchy)
    (p0 pt : Finset J → (J → ℂ) →
      {p : PosPoly // Gtest.positiveTime p})
    (hS0lim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto
        (fun k => (Gtest.reflectedPolynomialMoment
          (Hcut k) (p0 s c).val (p0 s c).val).re) l
        (𝓝 (Gtest.reflectedPolynomialMoment
          Hsch (p0 s c).val (p0 s c).val).re))
    (hStlim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto
        (fun k => (Gtest.reflectedPolynomialMoment
          (Hcut k) (p0 s c).val (pt s c).val).re) l
        (𝓝 (Gtest.reflectedPolynomialMoment
          Hsch (p0 s c).val (pt s c).val).re))
    (hMatch0 : ∀ (s : Finset J) (c : J → ℂ),
      (Gtest.reflectedPolynomialMoment
        Hsch (p0 s c).val (p0 s c).val).re =
      ‖∑ j ∈ s, c j • v j‖ ^ 2)
    (hMatcht : ∀ (s : Finset J) (c : J → ℂ),
      (Gtest.reflectedPolynomialMoment
        Hsch (p0 s c).val (pt s c).val).re =
      (⟪Tcont (∑ j ∈ s, c j • v j),
        ∑ j ∈ s, c j • v j⟫_ℂ).re)
    (err : Cut → ℝ)
    (cost : Finset J → (J → ℂ) → ℝ)
    (herr0 : Tendsto err l (𝓝 0))
    (hcut : ∀ (s : Finset J) (c : J → ℂ),
      ∀ᶠ k in l,
        (Gtest.reflectedPolynomialMoment
          (Hcut k) (p0 s c).val (pt s c).val).re ≤
        Real.exp (-t * d) *
          (Gtest.reflectedPolynomialMoment
            (Hcut k) (p0 s c).val (p0 s c).val).re +
        err k * cost s c) :
    Original42ContinuumOnlyMain OmegaCont Acont
      (stagesFromOSHierarchy Phase Joint Local Nontrivial
        Gtest PublishedOS Hsch) d := by
  let Q0 : Cut → Finset J → (J → ℂ) → ℝ := fun k s c =>
    (Gtest.reflectedPolynomialMoment
      (Hcut k) (p0 s c).val (p0 s c).val).re
  let Qt : Cut → Finset J → (J → ℂ) → ℝ := fun k s c =>
    (Gtest.reflectedPolynomialMoment
      (Hcut k) (p0 s c).val (pt s c).val).re
  have hQ0lim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Q0 k s c) l
        (𝓝 (‖∑ j ∈ s, c j • v j‖ ^ 2)) := by
    intro s c
    simpa only [Q0, hMatch0 s c] using hS0lim s c
  have hQtlim : ∀ (s : Finset J) (c : J → ℂ),
      Tendsto (fun k => Qt k s c) l
        (𝓝 (⟪Tcont (∑ j ∈ s, c j • v j),
          ∑ j ∈ s, c j • v j⟫_ℂ).re) := by
    intro s c
    simpa only [Qt, hMatcht s c] using hStlim s c
  exact original42_continuum_only_from_asymptotic_gram
    Phase Joint Local Nontrivial
    Gtest PublishedOS Hsch hOS
    hPhase hJoint hLocal hNontrivial
    OmegaCont v Tcont Acont
    t d ht hd hcalc hdense
    Q0 Qt hQ0lim hQtlim err cost herr0
    (by
      intro s c
      exact hcut s c)

#print axioms original42_continuum_only_from_same_schwinger_gram

end YMUIC.Original42
