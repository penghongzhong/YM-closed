import Mathlib

set_option autoImplicit false

/-!
Standalone type certificate for v133 theorem `thm:U1`.

This does NOT re-prove the Balaban papers. It checks that the manuscript uses
the published U1 input through an explicit, narrow interface. The analytic
content is classified as EXTERNAL-INTERFACE, not as an internal Lean proof.
-/

namespace YMUICV128.Section02

structure U1Data (polymer background : Type*) where
  H : ℕ → polymer → background → ℂ
  oldR : ℕ → polymer → background → ℂ
  newR : ℕ → polymer → background → ℂ
  d : ℕ → polymer → ℝ
  g : ℕ → ℝ
  Asf : ℕ → ℝ
  gamma : ℝ
  Csf0 : ℝ
  CR : ℝ
  CRnew : ℝ
  kappaPub : ℝ
  kappaR : ℝ
  kappa0 : ℝ
  p0 : ℝ → ℝ
  localizedClass : ℕ → background → Prop

structure U1PublishedHypotheses
    {polymer background : Type*}
    (D : U1Data polymer background) : Prop where
  gammaRange : 0 < D.gamma ∧ D.gamma < 1
  sfBound :
    ∀ (j : ℕ) (X : polymer) (ω : background),
      0 < D.g j → D.g j ≤ D.gamma →
      ‖D.H j X ω‖ ≤
        D.Csf0 * D.Asf j * Real.exp (-D.kappaPub * D.d j X)
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
  preserves :
    ∀ (j : ℕ) (ω : background),
      0 < D.g j → D.g j ≤ D.gamma →
      D.localizedClass (j + 1) ω

theorem u1_exact_interface_use
    {polymer background : Type*}
    (D : U1Data polymer background)
    (P : U1PublishedHypotheses D)
    {j : ℕ} {X : polymer} {ω : background}
    (hg0 : 0 < D.g j) (hgw : D.g j ≤ D.gamma) :
    ‖D.H j X ω‖ ≤
        D.Csf0 * D.Asf j * Real.exp (-D.kappaPub * D.d j X)
    ∧
    ‖D.oldR j X ω‖ ≤
        D.CR * Real.rpow (D.g j) D.kappa0 *
          Real.exp (-D.kappaR * D.d j X)
    ∧
    ‖D.newR j X ω‖ ≤
        D.CRnew * Real.exp (-D.p0 (D.g j)) *
          Real.exp (-D.kappaR * D.d j X)
    ∧
    D.localizedClass (j + 1) ω := by
  exact ⟨P.sfBound j X ω hg0 hgw,
    P.oldRBound j X ω hg0 hgw,
    P.newRBound j X ω hg0 hgw,
    P.preserves j ω hg0 hgw⟩

#print axioms u1_exact_interface_use

end YMUICV128.Section02
