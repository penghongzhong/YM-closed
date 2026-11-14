import YMOriginal.Original01_U1PublishedBridge

set_option autoImplicit false
noncomputable section

namespace YMUICV128.Section02

/-!
# Published Bałaban input bundle, split by paper provenance

External sources supplied by the user and used as published inputs:
* Bałaban, Renormalization Group Approach to Lattice Gauge Field Theories I:
  small-field localized effective actions and weak-coupling bounds.
* Bałaban, Part II: Cluster Expansions:
  localization of the fluctuation integral and preservation of the inductive
  small-field class.
* Bałaban, Convergent Renormalization Expansions for Lattice Gauge Theories:
  complete densities including large-field domains and the R-operation.

Lean does not re-prove those papers.  It checks that the exact numerical
inequalities used later are exposed as typed fields and that the three
published pieces assemble to the existing U1 published interface.
-/

structure PublishedBalabanSmallField
    {polymer background : Type*}
    (D : U1Data polymer background) : Prop where
  gammaRange : 0 < D.gamma ∧ D.gamma < 1
  sfBound :
    ∀ (j : ℕ) (X : polymer) (ω : background),
      0 < D.g j → D.g j ≤ D.gamma →
      ‖D.H j X ω‖ ≤
        D.Csf0 * D.Asf j * Real.exp (-D.kappaPub * D.d j X)

structure PublishedBalabanClusterLocalization
    {polymer background : Type*}
    (D : U1Data polymer background) : Prop where
  preserves :
    ∀ (j : ℕ) (ω : background),
      0 < D.g j → D.g j ≤ D.gamma →
      D.localizedClass (j + 1) ω

structure PublishedBalabanCompleteRT
    {polymer background : Type*}
    (D : U1Data polymer background) : Prop where
  oldRBound :
    ∀ (j : ℕ) (X : polymer) (ω : background),
      0 < D.g j → D.g j ≤ D.gamma →
      ‖D.oldR j X ω‖ ≤
        D.CR * Real.rpow (D.g j) D.kappa0 *
          Real.exp (-D.kappaR * D.d j X)
  newRBound :
    ∀ (j : ℕ) (X : polymer) (ω : background),
      0 < D.g j → D.g j ≤ D.gamma →
      ‖D.newR j X ω‖ ≤
        D.CRnew * Real.exp (-D.p0 (D.g j)) *
          Real.exp (-D.kappaR * D.d j X)

/-- The three published Bałaban inputs give exactly the pre-existing narrow
U1 interface used by all downstream Original24 modules. -/
theorem u1PublishedHypotheses_of_balaban_bundle
    {polymer background : Type*}
    (D : U1Data polymer background)
    (I : PublishedBalabanSmallField D)
    (II : PublishedBalabanClusterLocalization D)
    (RT : PublishedBalabanCompleteRT D) :
    U1PublishedHypotheses D := by
  exact
    { gammaRange := I.gammaRange
      sfBound := I.sfBound
      oldRBound := RT.oldRBound
      newRBound := RT.newRBound
      preserves := II.preserves }

#print axioms u1PublishedHypotheses_of_balaban_bundle

end YMUICV128.Section02
