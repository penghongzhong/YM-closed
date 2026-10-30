import YMOriginal.Original24_ExactRealTwoRootFPSeries
import YMOriginal.Original24_FromPublishedU1ConnectedFP
import YMOriginal.Original24_ActualLatticeLinks

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open YMUICV128.Section02

/-!
# Real Bałaban U1 old/new R -> literal full connected two-root Wilson sums

The prior exact-graph infinite-series theorem takes an abstract
polymer activity z. This terminal specialisation uses exactly the
PUBLISHED original U1Data.oldR and U1Data.newR functions at the
SAME RG scale j and SAME background omega, with the same native
finite history species Γ, physical support, length dictionary
and true four-dimensional periodic cutoff N.

The real U1 *local norm* is DERIVED, not postulated, by the
already checked original24_real_U1_old_new_local_norm from
Balaban pointwise old/new-R decay and an explicitly required
UNMARKED history count.

The only new graph combinatorial input is the PHYSICAL exact
two-root finite-height FP criterion for each original sector.
These are exact n+2-vertex graph statements with 1/n! and not
the stronger desired full connected norm/series conclusion.

A direct source-jet identification with published CMP119/122,
uniform unmarked history counting and fixed-D counterterm is
still REQUIRED before Original24 can be counted as original
manuscript B11 fully verified.
-/

/-- Genuine same-history, same-background, two-sector full exact
SU2 connected Wilson Mayer summability, with a non-assumed
physical O(aAct) bound derived from printed published U1 and the
exact tree-enumeration interface.

No arbitrary Phi_n, no assumed complete cluster bound, no
source-deformed CMP large-field R analyticity, and no full-series
convergence hypothesis. -/
theorem original24_balaban_real_old_new_complete_two_root_series
    (Pub : PublishedPenroseExtendedTwoRoot)
    {Γ Ω T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (D : U1Data Γ Ω) (pub : U1PublishedHypotheses D)
    (N chi j : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (hdictionary : ∀ X, D.d j X = (d X : ℝ))
    (rootP rootQ : Finset (PeriodicBlock N))
    (kappa mu cGeo Ccount : ℝ)
    (hCount : 0 ≤ Ccount)
    (hcount : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount)
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmallOld :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
       (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount) ≤
       kappa - cGeo * mu)
    (hsmallNew :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
       (newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount) ≤
       kappa - cGeo * mu)
    (hFPold : PhysicalExactTwoRootFPCriterion N chi
      rootP rootQ support (fun X => D.oldR j X omega) d cGeo mu)
    (hFPnew : PhysicalExactTwoRootFPCriterion N chi
      rootP rootQ support (fun X => D.newR j X omega) d cGeo mu)
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
    (hActOld : 0 <
      oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount)
    (hActNew : 0 <
      newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount) :
    let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
      fun w => actualWalkHolonomy links base w.vertices
    let K : ℝ := (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
    ∃ C_old C_new : ℝ, 0 ≤ C_old ∧ 0 ≤ C_new ∧
      Summable (fun n : ℕ =>
        actualTwoRootInsertion U wp cp wq cq s t *
          actualExactBalabanOldRTwoRootTerm D j (n + 1)
            N chi omega rootP rootQ support) ∧
      Summable (fun n : ℕ =>
        actualTwoRootInsertion U wp cp wq cq s t *
          actualExactBalabanNewRTwoRootTerm D j (n + 1)
            N chi omega rootP rootQ support) ∧
      (∑' n : ℕ,
        ‖actualTwoRootInsertion U wp cp wq cq s t *
          actualExactBalabanOldRTwoRootTerm D j (n + 1)
            N chi omega rootP rootQ support‖) ≤
          K * C_old *
            (oldRActivityFactor
              (D.g j) D.kappa0 D.CR * Ccount) ∧
      (∑' n : ℕ,
        ‖actualTwoRootInsertion U wp cp wq cq s t *
          actualExactBalabanNewRTwoRootTerm D j (n + 1)
            N chi omega rootP rootQ support‖) ≤
          K * C_new *
            (newRActivityFactor
              (D.g j) D.CRnew D.p0 * Ccount) := by
  dsimp
  obtain ⟨hLocalOld, hLocalNew⟩ :=
    original24_real_U1_old_new_local_norm
      D pub N j omega support d hdictionary kappa Ccount hcount
      hg hgw hCR hCRnew
  let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
    fun w => actualWalkHolonomy links base w.vertices
  obtain ⟨Cold, hCold, hSummableOld, hNormOld, hTotalOld⟩ :=
    actual_original24_two_root_mayer_full_sum_from_U1_FP
      Pub N chi rootP rootQ support
      (fun X => D.oldR j X omega) d
      kappa mu cGeo
      (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount)
      hActOld hdelta hsize hsmallOld hLocalOld hFPold
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  obtain ⟨Cnew, hCnew, hSummableNew, hNormNew, hTotalNew⟩ :=
    actual_original24_two_root_mayer_full_sum_from_U1_FP
      Pub N chi rootP rootQ support
      (fun X => D.newR j X omega) d
      kappa mu cGeo
      (newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount)
      hActNew hdelta hsize hsmallNew hLocalNew hFPnew
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  exact ⟨Cold, Cnew, hCold, hCnew, hSummableOld,
    hSummableNew, hTotalOld, hTotalNew⟩

end YMUIC.Original24
