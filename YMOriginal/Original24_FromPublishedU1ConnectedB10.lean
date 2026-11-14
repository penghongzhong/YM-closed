import YMOriginal.Original24_FromPublishedU1ConnectedFP
import YMOriginal.Original24_ConnectedWilsonB10

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open YMUICV128.Section02

/-!
# Original24: C29 real Bałaban U1 old/new R -> actual connected B10

The real old/new source histograms come directly from the UNCHANGED
published U1Data at the SAME j and omega.  The same periodic physical
history-index Γ, length d and root-support dictionary applies to
both.  The per-block U1 activity estimates are derived from the
published pointwise old/new R bounds plus the explicitly separated
unmarked history-count input.  The physical Schwartz fifth-order
Taylor bound is then produced by the checked connected Penrose/FP
rooted recursion.

No hB10 remainder estimate, arbitrary source-deformed R operation,
already-summable marked clusters, or terminal LF_D closure is passed
as a premise.

Outstanding: actual published CMP history-to-Γ/count dictionary,
the precise external Penrose/FP specialization, and finite-D jet /
counterterm projection remain separate, named model obligations.
-/

/-- Simultaneous old/new actual Wilson large-field connected fifth
Taylor remainder from published Balaban U1. The output is an explicit
TRUE 4D Schwartz-source, full-radius, finite history truncation
estimate at every cutoff, not a source-norm hypothesis. -/
theorem original24_balaban_old_new_connected_B10
    {Γ Ω T S : Type*} [Fintype Γ] [Fintype T] [Fintype S]
    (D : U1Data Γ Ω) (pub : U1PublishedHypotheses D)
    (N chi j : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (hdictionary : ∀ X, D.d j X = (d X : ℝ))
    (root : Finset (PeriodicBlock N))
    (kappa mu cGeo Ccount : ℝ)
    (hcount : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount)
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew)
    (hCount : 0 ≤ Ccount)
    (hmu : 0 < mu)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hweakOld :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount) ≤
          (kappa - cGeo * mu) / 2)
    (hweakNew :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount) ≤
          (kappa - cGeo * mu) / 2)
    (base : PeriodicBlock N)
    (links : PeriodicBlock N → PeriodicBlock N → SU2)
    (wp : T → List (List (ClosedLinkWalkAt (PeriodicBlock N) base)))
    (cp : T → ℂ)
    (wq : S → List (List (ClosedLinkWalkAt (PeriodicBlock N) base)))
    (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (PhiOld PhiNew : ℕ → ℂ)
    (position displacement : ℕ → TestSpace4)
    (treeOld treeNew : ℕ → ℝ)
    (hPenroseOld : ∀ n,
      ‖PhiOld n‖ * Real.exp (mu * ‖displacement n‖) ≤ treeOld n)
    (hPenroseNew : ∀ n,
      ‖PhiNew n‖ * Real.exp (mu * ‖displacement n‖) ≤ treeNew n)
    (hFPold : ∀ n,
      (∑ k ∈ Finset.range n, treeOld k) ≤
        actualPeriodicFirstRootSum N chi root support
          (fun X => D.oldR j X omega) d cGeo mu n)
    (hFPnew : ∀ n,
      (∑ k ∈ Finset.range n, treeNew k) ≤
        actualPeriodicFirstRootSum N chi root support
          (fun X => D.newR j X omega) d cGeo mu n)
    (f : SchwartzMap TestSpace4 ℂ)
    (aJ aN Mf : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN) (hMf : 0 ≤ Mf)
    (hTest : SchwartzMap.seminorm ℂ 0 5 f ≤ Mf / aN ^ 5) :
    let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
      fun w => actualWalkHolonomy links base w.vertices
    let K : ℝ :=
      (Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)
    let Croot : ℝ :=
      ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ))
    ∀ m : ℕ,
      (‖finiteMarkedTaylorRemainder
        (fun i : Fin m =>
          actualTwoRootInsertion U wp cp wq cq s t * PhiOld i.val)
        (actualSchwartzTaylorLine f
          (fun i : Fin m => position i.val)
          (fun i : Fin m => displacement i.val) aJ)‖ ≤
        (5 * (K * (Croot * (oldRActivityFactor
          (D.g j) D.kappa0 D.CR * Ccount))) / mu ^ 5) *
          Mf * (aJ / aN) ^ 5) ∧
      (‖finiteMarkedTaylorRemainder
        (fun i : Fin m =>
          actualTwoRootInsertion U wp cp wq cq s t * PhiNew i.val)
        (actualSchwartzTaylorLine f
          (fun i : Fin m => position i.val)
          (fun i : Fin m => displacement i.val) aJ)‖ ≤
        (5 * (K * (Croot * (newRActivityFactor
          (D.g j) D.CRnew D.p0 * Ccount))) / mu ^ 5) *
          Mf * (aJ / aN) ^ 5) := by
  dsimp
  have hAold : 0 ≤
      oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount :=
    mul_nonneg
      (mul_nonneg hCR (Real.rpow_pos_of_pos hg _).le) hCount
  have hAnew : 0 ≤
      newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount :=
    mul_nonneg
      (mul_nonneg hCRnew (Real.exp_pos _).le) hCount
  obtain ⟨hLocalOld, hLocalNew⟩ :=
    original24_real_U1_old_new_local_norm
      D pub N j omega support d hdictionary kappa Ccount hcount
      hg hgw hCR hCRnew
  let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
    fun w => actualWalkHolonomy links base w.vertices
  have hOld :=
    original24_connected_Wilson_B10_from_U1_FP
      N chi root support (fun X => D.oldR j X omega) d
      kappa mu cGeo
      (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount)
      hAold hdelta hsize hweakOld hLocalOld
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
      PhiOld position displacement treeOld hmu
      hPenroseOld hFPold f aJ aN Mf haJ haN hMf hTest
  have hNew :=
    original24_connected_Wilson_B10_from_U1_FP
      N chi root support (fun X => D.newR j X omega) d
      kappa mu cGeo
      (newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount)
      hAnew hdelta hsize hweakNew hLocalNew
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
      PhiNew position displacement treeNew hmu
      hPenroseNew hFPnew f aJ aN Mf haJ haN hMf hTest
  intro m
  exact ⟨hOld m, hNew m⟩

end YMUIC.Original24
