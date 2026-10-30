import YMOriginal.Original01_U1PublishedBridge
import YMOriginal.Original24_TwoRootOldNewU1
import YMOriginal.Original24_ActualLatticeLinks

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open YMUICV128.Section02

/-!
# Direct C29 Original24 link: published U1 Balaban -> TRUE 2-root Wilson R

The full-radius source roots are actual ordered closed paths of real
SU(2) LATTICE LINK VARIABLES, not abstract Wilson-root input symbols.
The old/new R history coefficients and their norm inequalities come
directly from the already audited and UNCHANGED published U1 interface
(the finite polymer/background g_j dependence is not rewritten).

The remaining upstream inputs (genuine connected root-to-root
support/length dictionary, same native history tree counting and
U2 rooted-tree bound) are explicitly original U2 model obligations.
They are not the marked-source conclusions and are not new axioms.

This is the actual bridge from the Balaban external theorem to the
original fixed-D two-root v57 source estimate, but we do not
unconditionally certify the model until these graph/model dictionaries
and the counterterm source jet are proved.
-/

/-- Two explicit bounded local gauge-invariant Wilson roots on genuine
SU(2) site-link variables use the SAME published U1 old/new-R
histories, backgrounds and running couplings. Under the original U2
rooted-tree inputs, derive C29 (317)--(319) without postulating any
source-deformed R-operation analytic stability. -/
theorem actual_link_two_root_from_exact_published_U1
    {polymer background Vertex T S : Type*} [Fintype T] [Fintype S]
    (D : U1Data polymer background)
    (pub : U1PublishedHypotheses D)
    (j : ℕ) (omega : background)
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew)
    (base : Vertex) (links : Vertex → Vertex → SU2)
    (wp : T → List (List (ClosedLinkWalkAt Vertex base)))
    (cp : T → ℂ)
    (wq : S → List (List (ClosedLinkWalkAt Vertex base)))
    (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (mu cGeo cRt dRoot : ℝ) (hmu : 0 ≤ mu)
    (hgeom : ∀ X, dRoot ≤ cRt + cGeo * D.d j X)
    (Nroot : ℕ)
    (hTreeOld : Summable (fun X : polymer =>
      oldRActivityFactor (D.g j) D.kappa0 D.CR *
        Real.exp (-(D.kappaR-mu*cGeo)*D.d j X)))
    (hTreeNew : Summable (fun X : polymer =>
      newRActivityFactor (D.g j) D.CRnew D.p0 *
        Real.exp (-(D.kappaR-mu*cGeo)*D.d j X)))
    (hU2Old :
      (∑' X : polymer, oldRActivityFactor (D.g j) D.kappa0 D.CR *
        Real.exp (-(D.kappaR-mu*cGeo)*D.d j X)) ≤
      (Nroot : ℝ) * oldRActivityFactor (D.g j) D.kappa0 D.CR)
    (hU2New :
      (∑' X : polymer, newRActivityFactor (D.g j) D.CRnew D.p0 *
        Real.exp (-(D.kappaR-mu*cGeo)*D.d j X)) ≤
      (Nroot : ℝ) * newRActivityFactor (D.g j) D.CRnew D.p0) :
    (∑' X : polymer,
      ‖actualTwoRootMarkedR
        (fun w : ClosedLinkWalkAt Vertex base =>
          actualWalkHolonomy links base w.vertices)
        wp cp wq cq s t (fun Y => D.oldR j Y omega) X‖) ≤
        ((Real.exp (radius * Bp) - 1) *
          (Real.exp (radius * Bq) - 1)) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
        oldRActivityFactor (D.g j) D.kappa0 D.CR *
          Real.exp (-mu * dRoot) ∧
    (∑' X : polymer,
      ‖actualTwoRootMarkedR
        (fun w : ClosedLinkWalkAt Vertex base =>
          actualWalkHolonomy links base w.vertices)
        wp cp wq cq s t (fun Y => D.newR j Y omega) X‖) ≤
        ((Real.exp (radius * Bp) - 1) *
          (Real.exp (radius * Bq) - 1)) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
        newRActivityFactor (D.g j) D.CRnew D.p0 *
          Real.exp (-mu * dRoot) := by
  have hOld (X : polymer) :
      ‖D.oldR j X omega‖ ≤
      oldRActivityFactor (D.g j) D.kappa0 D.CR *
        Real.exp (-D.kappaR * D.d j X) := by
    simpa only [oldRActivityFactor] using
      pub.oldRBound j X omega hg hgw
  have hNew (X : polymer) :
      ‖D.newR j X omega‖ ≤
      newRActivityFactor (D.g j) D.CRnew D.p0 *
        Real.exp (-D.kappaR * D.d j X) := by
    simpa only [newRActivityFactor] using
      pub.newRBound j X omega hg hgw
  exact actual_two_root_old_new_r_full_radius
    (fun w : ClosedLinkWalkAt Vertex base =>
      actualWalkHolonomy links base w.vertices)
    wp cp wq cq s t radius Bp Bq
    hr hp0 hq0 hs ht hp hq
    (fun X => D.oldR j X omega)
    (fun X => D.newR j X omega)
    (D.d j) (D.g j) D.kappa0 D.kappaR D.CR D.CRnew D.p0
    hg hCR hCRnew
    mu cGeo cRt dRoot hmu hgeom hOld hNew
    Nroot hTreeOld hTreeNew hU2Old hU2New

end YMUIC.Original24
