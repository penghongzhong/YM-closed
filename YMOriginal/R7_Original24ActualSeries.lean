import YMOriginal.R7_PublishedFPActualCriterion
import YMOriginal.Original24_BalabanTwoRootRealFullSeries
import YMOriginal.Original24_NativeShellU1

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section02
open YMUICV128.Section03

/-!
# R7 Original24: actual Bałaban two-root series with no model hFP premise

This wrapper removes two former model-facing assumptions at once:
* the weighted per-block native activity norm is derived from the
  published pointwise decay plus the actual shell-count geometry;
* the exact physical two-root FP criterion is derived internally from
  the generic published single-q rooted-tree enumeration.

The remaining external combinatorics are precisely the published
Penrose and Fernández--Procacci interfaces.
-/

/-- Complete old/new actual Wilson two-root connected series from the
registered U1 data and native shell geometry, with the model-specific
hFP hypotheses discharged. -/
theorem r7_balaban_old_new_complete_two_root_series
    (Penrose : PublishedPenroseExtendedTwoRoot)
    (FP : PublishedFPPeriodicSingleQ)
    {Γ Ω T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (D : U1Data Γ Ω) (pub : U1PublishedHypotheses D)
    (N chi j : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (hdictionary : ∀ X, D.d j X = (d X : ℝ))
    (rootP rootQ : Finset (PeriodicBlock N))
    (kappa mu cGeo Cpol cpol : ℝ)
    (hCpol : 0 ≤ Cpol)
    (hgap : 0 < D.kappaR - kappa - cpol)
    (hShell : ∀ Delta : PeriodicBlock N, ∀ m : ℕ,
      ((actualThroughBlock support Delta).filter
        (fun X => d X = m)).card ≤
          Cpol * Real.exp (cpol * (m : ℝ)))
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmallOld :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
       (oldRActivityFactor (D.g j) D.kappa0 D.CR *
        (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ≤
       kappa - cGeo * mu)
    (hsmallNew :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
       (newRActivityFactor (D.g j) D.CRnew D.p0 *
        (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ≤
       kappa - cGeo * mu)
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
      oldRActivityFactor (D.g j) D.kappa0 D.CR *
      (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))))
    (hActNew : 0 <
      newRActivityFactor (D.g j) D.CRnew D.p0 *
      (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) :
    let Ccount : ℝ :=
      Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))
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
  let Ccount : ℝ :=
    Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))
  have hcount : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount :=
    actual_native_U1_shell_count_to_block_norm
      support d Cpol cpol D.kappaR kappa hCpol hgap hShell
  have hFPold : PhysicalExactTwoRootFPCriterion N chi
      rootP rootQ support (fun X => D.oldR j X omega) d cGeo mu :=
    r7_actual_two_root_fp_criterion FP N chi rootP rootQ support
      (fun X => D.oldR j X omega) d cGeo mu
  have hFPnew : PhysicalExactTwoRootFPCriterion N chi
      rootP rootQ support (fun X => D.newR j X omega) d cGeo mu :=
    r7_actual_two_root_fp_criterion FP N chi rootP rootQ support
      (fun X => D.newR j X omega) d cGeo mu
  exact original24_balaban_real_old_new_complete_two_root_series
    Penrose D pub N chi j omega support d hdictionary rootP rootQ
    kappa mu cGeo Ccount hcount hg hgw hCR hCRnew hdelta hsize
    hsmallOld hsmallNew hFPold hFPnew
    base links wp cp wq cq s t radius Bp Bq
    hr hp0 hq0 hs ht hp hq hActOld hActNew

#print axioms r7_balaban_old_new_complete_two_root_series

end YMUIC.Original24
