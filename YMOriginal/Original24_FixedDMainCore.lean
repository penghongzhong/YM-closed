import YMOriginal.Original24_NativeShellU1
import YMOriginal.Original24_ExactRealTwoRootFPSeries
import YMConditional.Original19_CountertermCocycle
import YMOriginal.Original24_ActualLatticeLinks
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section02
open YMUICV128.Section03
open YMUIC.Counterterm
open Filter Topology

/-!
# Original24 B11: one FIXED-D terminal original-model core

This checks the SAME physical Bałaban U1 oldR/newR polymer fields,
SAME RG step/background, exact n+2 hard-core Wilson-Mayer graphs,
true SU2 lattice Wilson sources, native integer polymer lengths
and ORIGINAL manuscript v133 shell-count geometry, then TRANSPORTS
their actual complete source series through the SAME B09/Original19
finite-dimensional source-jet projection and ordered RG mixing
cocycle.

Unlike earlier independent helper lemmas, one theorem environment
simultaneously proves:
  - absolute summability of BOTH exact physical two-root sectors;
  - quantitative norm of their complete sum;
  - cutoff- and dimension-independent source-lift norm bound
    (provided the physical source lift is uniformly bounded);
  - existence of a single invertible fixed-D RG cocycle;
  - exact dual pairing and splitting of the SAME source into
    local jet and the complementary remainder.

Explicit unresolved upstream MATHEMATICAL inputs remain:
  * PublishedPenroseExtendedTwoRoot: exact universal hard-core
    Penrose tree graph inequality, clearly external;
  * PhysicalExactTwoRootFPCriterion old/new: the actual,
    not yet Lean-proved, physical FP finite-height enumeration;
  * real native shell count and original old/new U1Data
    background-to-physical-polymer identification;
  * the physical source lift / fixed-D jet map identifying the
    scalar Mayer functional with the actual R-sector source chart;
  * the fifth-order MARKED B10 remainder and its true
    RG/local-counterterm source-class localization.
Thus this theorem is NOT the unchanged manuscript B11=CLOSED yet.
-/

/-- Terminal direct core for every actual fixed finite jet dimension Ddim:
the full old/new SU2 two-root Mayer source, already controlled by
published-U1/native-shell/Penrose/FP, undergoes an ACTUAL ordered
invertible source counterterm cocycle and an EXACT source jet
subtraction. The full distribution/source norm bound is proved
from the convergent physical series, not assumed as an input.

No source-jet remainder bound or U1 marked-R stability appears among
the assumptions; the precise physics-to-lift dictionary still must
be checked before counting this as original environment #24. -/
theorem original24_fixedD_same_source_full_series_and_cocycle
    {F ι Ω Γ T S : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype Γ] [Fintype T] [Fintype S]
    (Ddim : ℕ)
    (M0 : EuclideanSpace ℝ (Fin Ddim) ≃L[ℝ] EuclideanSpace ℝ (Fin Ddim))
    (M : ι → ℝ →
      EuclideanSpace ℝ (Fin Ddim) →L[ℝ] EuclideanSpace ℝ (Fin Ddim))
    (modulus : ℝ → ℝ) (gMax : ℝ) (hgMax : 0 < gMax)
    (hmodulus : Tendsto modulus (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hmod : ∀ i g, 0 < g → g ≤ gMax →
      ‖M i g - (M0 :
        EuclideanSpace ℝ (Fin Ddim) →L[ℝ]
        EuclideanSpace ℝ (Fin Ddim))‖ ≤ modulus g)
    (extract : F →L[ℝ] EuclideanSpace ℝ (Fin Ddim))
    (includeJet : EuclideanSpace ℝ (Fin Ddim) →L[ℝ] F)
    (hjet : extract.comp includeJet =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin Ddim)))
    (sourceLift : ℂ →L[ℝ] F)
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
    (Pub : PublishedPenroseExtendedTwoRoot)
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
      oldRActivityFactor (D.g j) D.kappa0 D.CR *
      (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))))
    (hActNew : 0 <
      newRActivityFactor (D.g j) D.CRnew D.p0 *
      (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) :
    let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
      fun w => actualWalkHolonomy links base w.vertices
    let K : ℝ :=
      (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
    let Aold : ℝ := oldRActivityFactor (D.g j) D.kappa0 D.CR *
      (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))
    let Anew : ℝ := newRActivityFactor (D.g j) D.CRnew D.p0 *
      (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))
    let oldTerm : ℕ → ℂ := fun n =>
      actualTwoRootInsertion U wp cp wq cq s t *
        actualExactBalabanOldRTwoRootTerm
          D j (n + 1) N chi omega rootP rootQ support
    let newTerm : ℕ → ℂ := fun n =>
      actualTwoRootInsertion U wp cp wq cq s t *
        actualExactBalabanNewRTwoRootTerm
          D j (n + 1) N chi omega rootP rootQ support
    let x : F :=
      sourceLift (∑' n, oldTerm n + newTerm n)
    ∃ gD Cold Cnew : ℝ,
      0 < gD ∧ gD ≤ gMax ∧ 0 ≤ Cold ∧ 0 ≤ Cnew ∧
      Summable (fun n : ℕ => oldTerm n + newTerm n) ∧
      ‖x‖ ≤ ‖sourceLift‖ *
        (K * (Cold * Aold + Cnew * Anew)) ∧
      ∀ (m : ℕ) (index : ℕ → ι) (g : ℕ → ℝ),
        (∀ j < m, 0 < g j ∧ g j ≤ gD) →
        ∃ Z : EuclideanSpace ℝ (Fin Ddim) ≃L[ℝ]
          EuclideanSpace ℝ (Fin Ddim),
          (Z : EuclideanSpace ℝ (Fin Ddim) →L[ℝ]
            EuclideanSpace ℝ (Fin Ddim)) =
             actualCocycle (fun j => M (index j) (g j)) m ∧
          ∀ J : EuclideanSpace ℝ (Fin Ddim) →L[ℝ] ℝ,
            transportedSource Z J (Z (extract x)) = J (extract x) ∧
            x = includeJet (extract x) +
              jetRemainder extract includeJet x ∧
            extract (jetRemainder extract includeJet x) = 0 := by
  dsimp
  let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
    fun w => actualWalkHolonomy links base w.vertices
  let K : ℝ :=
    (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
  let Ccount : ℝ :=
    Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))
  let Aold : ℝ := oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount
  let Anew : ℝ := newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount
  let oldTerm : ℕ → ℂ := fun n =>
    actualTwoRootInsertion U wp cp wq cq s t *
      actualExactBalabanOldRTwoRootTerm
        D j (n + 1) N chi omega rootP rootQ support
  let newTerm : ℕ → ℂ := fun n =>
    actualTwoRootInsertion U wp cp wq cq s t *
      actualExactBalabanNewRTwoRootTerm
        D j (n + 1) N chi omega rootP rootQ support
  let x : F := sourceLift (∑' n, oldTerm n + newTerm n)
  have hcount : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount :=
    actual_native_U1_shell_count_to_block_norm
      support d Cpol cpol D.kappaR kappa hCpol hgap hShell
  obtain ⟨hLocalOld, hLocalNew⟩ :=
    original24_real_U1_old_new_local_norm
      D pub N j omega support d hdictionary kappa Ccount hcount
      hg hgw hCR hCRnew
  obtain ⟨Cold, hCold, hsOld, hnOld, hbOld⟩ :=
    actual_original24_two_root_mayer_full_sum_from_U1_FP
      Pub N chi rootP rootQ support
      (fun X => D.oldR j X omega) d
      kappa mu cGeo Aold hActOld hdelta hsize
      hsmallOld hLocalOld hFPold
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  obtain ⟨Cnew, hCnew, hsNew, hnNew, hbNew⟩ :=
    actual_original24_two_root_mayer_full_sum_from_U1_FP
      Pub N chi rootP rootQ support
      (fun X => D.newR j X omega) d
      kappa mu cGeo Anew hActNew hdelta hsize
      hsmallNew hLocalNew hFPnew
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  have hsum : Summable (fun n : ℕ => oldTerm n + newTerm n) :=
    hsOld.add hsNew
  have hsumNorm : Summable (fun n : ℕ =>
      ‖oldTerm n + newTerm n‖) :=
    Summable.of_nonneg_of_le
      (fun n => norm_nonneg _)
      (fun n => norm_add_le _ _)
      (hnOld.add hnNew)
  have hK : 0 ≤ K := by
    dsimp [K]
    apply mul_nonneg
    · exact sub_nonneg.mpr
        (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
    · exact sub_nonneg.mpr
        (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have htotal :
      ‖∑' n, oldTerm n + newTerm n‖ ≤
      K * (Cold * Aold + Cnew * Anew) := by
    calc
      _ ≤ ∑' n : ℕ, ‖oldTerm n + newTerm n‖ :=
        norm_tsum_le_tsum_norm hsumNorm
      _ ≤ ∑' n : ℕ, (‖oldTerm n‖ + ‖newTerm n‖) :=
        hsumNorm.tsum_le_tsum
          (fun n => norm_add_le _ _) (hnOld.add hnNew)
      _ = (∑' n : ℕ, ‖oldTerm n‖) +
          (∑' n : ℕ, ‖newTerm n‖) := hnOld.tsum_add hnNew
      _ ≤ K * Cold * Aold + K * Cnew * Anew :=
        add_le_add hbOld hbNew
      _ = K * (Cold * Aold + Cnew * Anew) := by ring
  have hx :
      ‖x‖ ≤ ‖sourceLift‖ *
        (K * (Cold * Aold + Cnew * Anew)) := by
    calc
      ‖x‖ = ‖sourceLift (∑' n, oldTerm n + newTerm n)‖ := rfl
      _ ≤ ‖sourceLift‖ *
        ‖∑' n, oldTerm n + newTerm n‖ :=
          sourceLift.le_opNorm _
      _ ≤ ‖sourceLift‖ *
          (K * (Cold * Aold + Cnew * Anew)) :=
          mul_le_mul_of_nonneg_left htotal (norm_nonneg _)
  obtain ⟨gD, hgD, hgDm, hblock⟩ :=
    original19_fixed_dimension_counterterm M0 M modulus hgMax
      hmodulus hmod
  refine ⟨gD, Cold, Cnew, hgD, hgDm, hCold, hCnew, hsum, hx, ?_⟩
  intro m index g hweak
  obtain ⟨Z, hZ, _hsteps, hdual⟩ := hblock m index g hweak
  refine ⟨Z, hZ, ?_⟩
  intro J
  have hsplit := jet_remainder_exact extract includeJet hjet x
  exact ⟨hdual J (extract x), hsplit.1, hsplit.2⟩

end YMUIC.Original24
