import YMOriginal.Original24_ExactRealTwoRootFPSeries
import YMOriginal.Original24_PublishedFPSingleQ
import YMOriginal.Original24_BalabanTwoRootRealFullSeries
import YMOriginal.Original24_ActualLatticeLinks

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section02
open YMUICV128.Section03

/-!
# Original24 from the published Bałaban local activity norm

Bałaban's complete-density theorem provides localized R-terms together
with uniform local sums (cf. Theorem 2, eq. (2.44), supplemented by the
single-domain exponential localization (2.42)).  Therefore the main
Original24 route need not reconstruct the local activity norm from a
separate shell-count hypothesis.

This theorem starts exactly at that published local-norm boundary, then
uses the universal Penrose and Fernández--Procacci interfaces plus the
internally proved physical two-root/single-q graph dictionary.
-/

theorem original24_complete_two_root_series_from_published_local_norm
    {Γ Ω T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (Pub : PublishedPenroseExtendedTwoRoot)
    (FP : PublishedFernandezProcacciSingleQ Γ)
    (D : U1Data Γ Ω)
    (N chi j : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (kappa mu cGeo Aold Anew : ℝ)
    (hgeom : 0 ≤ cGeo * mu)
    (hAold : 0 < Aold) (hAnew : 0 < Anew)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmallOld :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * Aold ≤
        kappa - cGeo * mu)
    (hsmallNew :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * Anew ≤
        kappa - cGeo * mu)
    (hLocalOld : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖D.oldR j X omega‖ * Real.exp (kappa * (d X : ℝ))) ≤ Aold)
    (hLocalNew : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖D.newR j X omega‖ * Real.exp (kappa * (d X : ℝ))) ≤ Anew)
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
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq) :
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
          K * C_old * Aold ∧
      (∑' n : ℕ,
        ‖actualTwoRootInsertion U wp cp wq cq s t *
          actualExactBalabanNewRTwoRootTerm D j (n + 1)
            N chi omega rootP rootQ support‖) ≤
          K * C_new * Anew := by
  dsimp
  let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
    fun w => actualWalkHolonomy links base w.vertices
  obtain ⟨Cold, hCold, hSummableOld, _hNormOld, hTotalOld⟩ :=
    actual_original24_two_root_mayer_full_sum_from_published_FP
      Pub FP N chi rootP rootQ support
      (fun X => D.oldR j X omega) d
      kappa mu cGeo Aold hgeom hAold hdelta hsize hsmallOld
      hLocalOld U wp cp wq cq s t radius Bp Bq
      hr hp0 hq0 hs ht hp hq
  obtain ⟨Cnew, hCnew, hSummableNew, _hNormNew, hTotalNew⟩ :=
    actual_original24_two_root_mayer_full_sum_from_published_FP
      Pub FP N chi rootP rootQ support
      (fun X => D.newR j X omega) d
      kappa mu cGeo Anew hgeom hAnew hdelta hsize hsmallNew
      hLocalNew U wp cp wq cq s t radius Bp Bq
      hr hp0 hq0 hs ht hp hq
  exact ⟨Cold, Cnew, hCold, hCnew,
    hSummableOld, hSummableNew, hTotalOld, hTotalNew⟩

#print axioms original24_complete_two_root_series_from_published_local_norm

end YMUIC.Original24
