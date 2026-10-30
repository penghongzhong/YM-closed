import YMOriginal.Original24_NativeShellU1
import YMOriginal.Original24_BalabanTwoRootRealFullSeries

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section02
open YMUICV128.Section03

/-!
# Original24 REAL Bałaban R-sector strict source, no free Ccount

From the original v133 U1 geometric shell count
  #(X containing Δ, d(X)=m) <= Cpol*exp(cpol*m),
the exact finite-shell combinatorial decomposition and geometric
series derive a uniform per-block unmarked history norm, using
only the published pointwise CMP119/122 old/new R bounds.

The earlier free hcount is ELIMINATED. This theorem composes
the derived shell norm with the previously kernel-verified
exact n+2 Wilson-Mayer/FP two-root complete series for BOTH
original RG sectors, with fixed full-radius SU2 Wilson roots.

Still explicit, NOT proved:
- physical hard-core CMP history identification;
- the actual n+2 two-root FP spanning-tree enumeration criterion;
- the original fixed-D source jets and RG counterterm identities.
The manuscript B11 original environment is not yet fully certified.
-/

theorem original24_balaban_native_shell_full_series
    (Pub : PublishedPenroseExtendedTwoRoot)
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
       (oldRActivityFactor (D.g j) D.kappa0 D.CR * (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ≤
       kappa - cGeo * mu)
    (hsmallNew :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
       (newRActivityFactor (D.g j) D.CRnew D.p0 * (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ≤
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
      oldRActivityFactor (D.g j) D.kappa0 D.CR * (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))))
    (hActNew : 0 <
      newRActivityFactor (D.g j) D.CRnew D.p0 * (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) :
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
              (D.g j) D.kappa0 D.CR * (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ∧
      (∑' n : ℕ,
        ‖actualTwoRootInsertion U wp cp wq cq s t *
          actualExactBalabanNewRTwoRootTerm D j (n + 1)
            N chi omega rootP rootQ support‖) ≤
          K * C_new *
            (newRActivityFactor
              (D.g j) D.CRnew D.p0 * (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) := by
  let Ccount : ℝ :=
    Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))
  have hcount : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount :=
    actual_native_U1_shell_count_to_block_norm
      support d Cpol cpol D.kappaR kappa hCpol hgap hShell
  simpa only [Ccount] using
    (original24_balaban_real_old_new_complete_two_root_series
      Pub D pub N chi j omega support d hdictionary
      rootP rootQ kappa mu cGeo Ccount hcount
      hg hgw hCR hCRnew hdelta hsize
      hsmallOld hsmallNew hFPold hFPnew
      base links wp cp wq cq
      s t radius Bp Bq hr hp0 hq0 hs ht hp hq
      hActOld hActNew)

end YMUIC.Original24
