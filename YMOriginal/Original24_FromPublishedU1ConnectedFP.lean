import YMOriginal.Original24_ConnectedUrsellFP
import YMOriginal.Original24_ActualLatticeLinks
import YMOriginal.Original01_U1PublishedBridge

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open YMUICV128.Section02

/-!
# Original24 real Balaban old/new-R to complete connected Wilson sources

This theorem does NOT treat arbitrary z as physical: z is literally
the same D.oldR and D.newR history evaluated at the same RG level,
same background and same cutoff. We prove the per-block U1 activity
norm from the *published* pointwise U1 bound and a separate
UNMARKED physical history-count input. We then use the already
verified all-height 4D KP root recursion and the explicit published
Penrose/FP finite-height interfaces to prove absolute convergence
of actual SU2 two-root connected cluster series in both sectors.

No marked-R source bound, full-series convergence, or desired
post-R conclusion is assumed. The exact actual-CMP119/122
connected-history encoding, source jet/counterterm matching, and
unmarked history count remain model obligations.
-/

/-- Derive a full unmarked per-block U1 history norm, not an assumed
marked bound. This is the precise counting task left when U1 provides
pointwise exp(-kappaR*d) estimates. -/
theorem original24_real_U1_old_new_local_norm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω) (pub : U1PublishedHypotheses D)
    (N j : ℕ) (ω : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (hdictionary : ∀ X, D.d j X = (d X : ℝ))
    (kappa Ccount : ℝ)
    (hcount : ∀ Δ : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Δ,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount)
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew) :
    (∀ Δ : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Δ,
        ‖D.oldR j X ω‖ * Real.exp (kappa * (d X : ℝ))) ≤
      oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount) ∧
    (∀ Δ : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Δ,
        ‖D.newR j X ω‖ * Real.exp (kappa * (d X : ℝ))) ≤
      newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount) := by
  let Aold := oldRActivityFactor (D.g j) D.kappa0 D.CR
  let Anew := newRActivityFactor (D.g j) D.CRnew D.p0
  have hAold : 0 ≤ Aold :=
    mul_nonneg hCR (Real.rpow_pos_of_pos hg _).le
  have hAnew : 0 ≤ Anew :=
    mul_nonneg hCRnew (Real.exp_pos _).le
  have he (X : Γ) :
      Real.exp (-D.kappaR * (d X : ℝ)) *
        Real.exp (kappa * (d X : ℝ)) =
      Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hOld (X : Γ) :
      ‖D.oldR j X ω‖ * Real.exp (kappa * (d X : ℝ)) ≤
      Aold * Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) := by
    have hU1 := pub.oldRBound j X ω hg hgw
    rw [hdictionary X] at hU1
    calc
      _ ≤
        (Aold * Real.exp (-D.kappaR * (d X : ℝ))) *
          Real.exp (kappa * (d X : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hU1 (Real.exp_pos _).le
      _ = Aold * Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) := by
        rw [mul_assoc, he]
  have hNew (X : Γ) :
      ‖D.newR j X ω‖ * Real.exp (kappa * (d X : ℝ)) ≤
      Anew * Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) := by
    have hU1 := pub.newRBound j X ω hg hgw
    rw [hdictionary X] at hU1
    calc
      _ ≤
        (Anew * Real.exp (-D.kappaR * (d X : ℝ))) *
          Real.exp (kappa * (d X : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hU1 (Real.exp_pos _).le
      _ = Anew * Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) := by
        rw [mul_assoc, he]
  constructor
  · intro Δ
    calc
      _ ≤ ∑ X ∈ actualThroughBlock support Δ,
          Aold * Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) :=
            Finset.sum_le_sum (fun X hX => hOld X)
      _ = Aold *
          (∑ X ∈ actualThroughBlock support Δ,
            Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ Aold * Ccount :=
        mul_le_mul_of_nonneg_left (hcount Δ) hAold
  · intro Δ
    calc
      _ ≤ ∑ X ∈ actualThroughBlock support Δ,
          Anew * Real.exp (-(D.kappaR - kappa) * (d X : ℝ)) :=
            Finset.sum_le_sum (fun X hX => hNew X)
      _ = Anew *
          (∑ X ∈ actualThroughBlock support Δ,
            Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ Anew * Ccount :=
        mul_le_mul_of_nonneg_left (hcount Δ) hAnew

/-- Physical, simultaneous old/new connected source estimates.
Every source is an actual finite ordered closed-link SU(2) polynomial,
with full radius and the SAME original U1 history fields.

The two registered published combinatorial interface fields are
pointwise Penrose domination and finite-height Fernández--Procacci
labeled-tree enumeration, separately for old and new histories.
No assumed infinite connected series bound is inserted. -/
theorem original24_real_U1_old_new_connected_Wilson
    {Γ Ω T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (D : U1Data Γ Ω) (pub : U1PublishedHypotheses D)
    (N chi j : ℕ) (ω : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (hdictionary : ∀ X, D.d j X = (d X : ℝ))
    (root : Finset (PeriodicBlock N))
    (kappa mu cGeo Ccount : ℝ)
    (hcount : ∀ Δ : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Δ,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount)
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew)
    (hCount : 0 ≤ Ccount)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hweakOld : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
       (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount) ≤
       (kappa - cGeo * mu) / 2)
    (hweakNew : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
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
    (treeOld treeNew : ℕ → ℝ)
    (hPenroseOld : ∀ n, ‖PhiOld n‖ ≤ treeOld n)
    (hPenroseNew : ∀ n, ‖PhiNew n‖ ≤ treeNew n)
    (hFPold : ∀ n,
      (∑ k ∈ Finset.range n, treeOld k) ≤
        actualPeriodicFirstRootSum N chi root support
          (fun X => D.oldR j X ω) d cGeo mu n)
    (hFPnew : ∀ n,
      (∑ k ∈ Finset.range n, treeNew k) ≤
        actualPeriodicFirstRootSum N chi root support
          (fun X => D.newR j X ω) d cGeo mu n) :
    let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
      fun w => actualWalkHolonomy links base w.vertices
    let K := (Real.exp (radius * Bp) - 1) *
             (Real.exp (radius * Bq) - 1)
    let Croot := ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ))
    (Summable (fun n => actualTwoRootInsertion U wp cp wq cq s t * PhiOld n) ∧
      (∑' n, ‖actualTwoRootInsertion U wp cp wq cq s t * PhiOld n‖) ≤
        K * (Croot * (oldRActivityFactor
          (D.g j) D.kappa0 D.CR * Ccount))) ∧
    (Summable (fun n => actualTwoRootInsertion U wp cp wq cq s t * PhiNew n) ∧
      (∑' n, ‖actualTwoRootInsertion U wp cp wq cq s t * PhiNew n‖) ≤
        K * (Croot * (newRActivityFactor
          (D.g j) D.CRnew D.p0 * Ccount))) := by
  dsimp
  have hAold : 0 ≤ oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount :=
    mul_nonneg
      (mul_nonneg hCR (Real.rpow_pos_of_pos hg _).le) hCount
  have hAnew : 0 ≤ newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount :=
    mul_nonneg
      (mul_nonneg hCRnew (Real.exp_pos _).le) hCount
  obtain ⟨hLocalOld, hLocalNew⟩ :=
    original24_real_U1_old_new_local_norm D pub N j ω
      support d hdictionary kappa Ccount hcount
      hg hgw hCR hCRnew
  let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
    fun w => actualWalkHolonomy links base w.vertices
  have hOld := original24_actual_two_root_connected_ursell
    N chi root support (fun X => D.oldR j X ω) d
    kappa mu cGeo
    (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount)
    hAold hdelta hsize hweakOld hLocalOld
    U wp cp wq cq s t radius Bp Bq
    hr hp0 hq0 hs ht hp hq
    PhiOld treeOld hPenroseOld hFPold
  have hNew := original24_actual_two_root_connected_ursell
    N chi root support (fun X => D.newR j X ω) d
    kappa mu cGeo
    (newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount)
    hAnew hdelta hsize hweakNew hLocalNew
    U wp cp wq cq s t radius Bp Bq
    hr hp0 hq0 hs ht hp hq
    PhiNew treeNew hPenroseNew hFPnew
  exact ⟨hOld, hNew⟩

end YMUIC.Original24
