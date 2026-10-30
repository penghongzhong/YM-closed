import YMOriginal.Original24_ActualPenroseWeighted
import YMOriginal.Original24_ActualLatticeLinks
import YMOriginal.Original24_TwoRootFullRadius

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open YMUICV128.Section02

/-!
# Original24: literal Wilson-source marked physical Mayer graph bound

Combine: (1) real two-root cluster coefficients from a finite
periodic hard-core incompatibility graph, (2) the EXACT published
universal finite Penrose spanning-tree estimate,
(3) actual SU2 ordered Wilson polynomial insertions at arbitrary
fixed complex source radius, and (4) the original Bałaban U1
old/new R coefficients at the SAME scale and background.

No auxiliary complex Phi_n or hypothesis about a marked coefficient
remains. The all-n FP/KP tree summation and exact CMP119/CMP122
history/jet/source-counterterm mapping remain open original-model
tasks and are not asserted here.
-/

/-- Full-radius SU2 two-root marked FINITE n+1-history Mayer term,
bounded by a true positive spanning-tree weight at the same cutoff. -/
theorem actual_physical_two_root_marked_penrose
    (Published : PublishedPenroseHardCoreTreeBound)
    {P T S Γ : Type*}
    [Fintype T] [Fintype S] [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq) :
    ‖actualTwoRootInsertion U wp cp wq cq s t *
      actualTwoRootHardCoreMayerTerm n N chi
        rootP rootQ support z‖ ≤
      ((Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)) *
      actualTwoRootSpanningTreeMajorant n N chi
        rootP rootQ support z := by
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
  have hKp : 0 ≤ Real.exp (radius * Bp) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hKq : 0 ≤ Real.exp (radius * Bq) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hKp hKq
  have hSrc :
      ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤ K :=
    actual_two_root_insertion_full_radius
      U wp cp wq cq s t radius Bp Bq
      hr hp0 hq0 hs ht hp hq
  have hTree :=
    actual_two_root_hardcore_penrose_weighted
      Published n N chi rootP rootQ support z
  rw [norm_mul]
  exact mul_le_mul hSrc hTree (norm_nonneg _) hK

/-- True SU2 lattice-link source, actual two physical Wilson
external roots, and literal oldR/newR Balaban history Mayer
coefficients at the SAME RG scale and SAME original background. -/
theorem actual_balaban_old_new_marked_penrose
    (Published : PublishedPenroseHardCoreTreeBound)
    {Γ Ω T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (D : U1Data Γ Ω)
    (j n N chi : ℕ) (omega : Ω)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
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
    let K : ℝ :=
      (Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)
    (‖actualTwoRootInsertion U wp cp wq cq s t *
        actualBalabanOldRTwoRootHardCoreTerm
          D j n N chi omega rootP rootQ support‖ ≤
       K * actualTwoRootSpanningTreeMajorant
         n N chi rootP rootQ support (fun X => D.oldR j X omega))
    ∧
    (‖actualTwoRootInsertion U wp cp wq cq s t *
        actualBalabanNewRTwoRootHardCoreTerm
          D j n N chi omega rootP rootQ support‖ ≤
       K * actualTwoRootSpanningTreeMajorant
         n N chi rootP rootQ support (fun X => D.newR j X omega)) := by
  dsimp
  exact ⟨
    actual_physical_two_root_marked_penrose Published
      n N chi rootP rootQ support (fun X => D.oldR j X omega)
      (fun w : ClosedLinkWalkAt (PeriodicBlock N) base =>
         actualWalkHolonomy links base w.vertices)
      wp cp wq cq s t radius Bp Bq
      hr hp0 hq0 hs ht hp hq,
    actual_physical_two_root_marked_penrose Published
      n N chi rootP rootQ support (fun X => D.newR j X omega)
      (fun w : ClosedLinkWalkAt (PeriodicBlock N) base =>
         actualWalkHolonomy links base w.vertices)
      wp cp wq cq s t radius Bp Bq
      hr hp0 hq0 hs ht hp hq⟩

end YMUIC.Original24
