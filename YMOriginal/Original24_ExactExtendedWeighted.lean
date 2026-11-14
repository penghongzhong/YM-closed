import YMOriginal.Original24_PublishedPenroseExtended
import YMOriginal.Original24_TwoRootFullRadius
import YMOriginal.Original24_ActualLatticeLinks

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open YMUICV128.Section02

/-!
# Correct manuscript extended two-root Penrose bound, literal source

This module uses EXACT C29 graph V = Fin n ⊕ {r_p,r_q}, with
the two root vertices INCLUDED in the connected Ursell sum,
no direct root-root bond, n bulk labeled histories and 1/n!.

The universal 2007 hard-core Penrose tree-graph theorem is the
ONLY external graph combinatorial theorem input, with its type
explicitly exposed. Neither a cluster coefficient Phi_n nor its
pointwise bound nor any full all-n tree-sum is assumed.

The final summation over n, physical CMP R history identification,
native root-distance and fixed-D source jets remain separate tasks.
-/

/-- Actual positive finite spanning-tree root sum with exact
1/n! symmetry weight and connected extended root graph. -/
def exactExtendedTwoRootTreeMajorant
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) : ℝ := by
  classical
  exact (Nat.factorial n : ℝ)⁻¹ *
    ∑ tuple : Fin n → Γ,
      if (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Connected then
        ((exactExtendedSpanningTrees n
          (actualExactTwoRootGraph n N chi rootP rootQ support tuple)).card : ℝ) *
        (∏ i : Fin n, ‖z (tuple i)‖)
      else 0

/-- Actual EXACT two-root Mayer connected coefficients, with BOTH
root vertices in graph, are bounded by the literal spanning-tree
sum term-by-term, then summed over labeled tuples with 1/n!.
This does not assume an arbitrary hPenrose on an abstract Phi. -/
theorem actual_exact_extended_two_root_penrose_weighted
    (Pub : PublishedPenroseExtendedTwoRoot)
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    ‖actualExactTwoRootMayerTerm n N chi rootP rootQ support z‖ ≤
      exactExtendedTwoRootTreeMajorant n N chi rootP rootQ support z := by
  classical
  let C : ℝ := (Nat.factorial n : ℝ)⁻¹
  let part : (Fin n → Γ) → ℂ := fun tuple =>
    if (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Connected then
      (actualExactTwoRootUrsellCoefficient
        n N chi rootP rootQ support tuple : ℂ) *
        (∏ i : Fin n, z (tuple i))
    else 0
  let bound : (Fin n → Γ) → ℝ := fun tuple =>
    if (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Connected then
      ((exactExtendedSpanningTrees n
        (actualExactTwoRootGraph n N chi rootP rootQ support tuple)).card : ℝ) *
        (∏ i : Fin n, ‖z (tuple i)‖)
    else 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCnorm : ‖((Nat.factorial n : ℂ)⁻¹)‖ = C := by
    simp [C]
  have hterm (tuple : Fin n → Γ) : ‖part tuple‖ ≤ bound tuple := by
    by_cases hConn :
        (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Connected
    · have hPen := actual_exact_extended_penrose
        Pub n N chi rootP rootQ support tuple
      have hProd : 0 ≤ ∏ i : Fin n, ‖z (tuple i)‖ :=
        Finset.prod_nonneg (fun i _ => norm_nonneg _)
      have hWeighted := mul_le_mul_of_nonneg_right hPen hProd
      simpa [part, bound, hConn, norm_mul, norm_prod,
        Complex.norm_real, Real.norm_eq_abs] using hWeighted
    · simp [part, bound, hConn]
  have hsum :
      ‖∑ tuple : Fin n → Γ, part tuple‖ ≤
        ∑ tuple : Fin n → Γ, bound tuple := by
    calc
      ‖∑ tuple : Fin n → Γ, part tuple‖ ≤
          ∑ tuple : Fin n → Γ, ‖part tuple‖ := norm_sum_le _ _
      _ ≤ ∑ tuple : Fin n → Γ, bound tuple :=
        Finset.sum_le_sum (fun tuple _ => hterm tuple)
  change ‖((Nat.factorial n : ℂ)⁻¹) *
    (∑ tuple : Fin n → Γ, part tuple)‖ ≤
    C * (∑ tuple : Fin n → Γ, bound tuple)
  rw [norm_mul, hCnorm]
  exact mul_le_mul_of_nonneg_left hsum hC

/-- Full-radius TRUE SU2 external source insertion times the exact
finite n+2-vertex rooted Mayer term, with the physical root-tree
majorant and correct factorial. -/
theorem actual_exact_extended_marked_penrose
    (Pub : PublishedPenroseExtendedTwoRoot)
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
      actualExactTwoRootMayerTerm n N chi rootP rootQ support z‖ ≤
      ((Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)) *
      exactExtendedTwoRootTreeMajorant n N chi rootP rootQ support z := by
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  have hpK : 0 ≤ Real.exp (radius * Bp) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hqK : 0 ≤ Real.exp (radius * Bq) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hpK hqK
  have hSrc : ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤ K :=
    actual_two_root_insertion_full_radius U wp cp wq cq
      s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  have hTree := actual_exact_extended_two_root_penrose_weighted
    Pub n N chi rootP rootQ support z
  rw [norm_mul]
  exact mul_le_mul hSrc hTree (norm_nonneg _) hK

/-- The SAME original U1Data.oldR/newR and true actual SU2 lattice
links at the SAME RG step produce both finite connected
root-source Penrose bounds. No arbitrary surrogate Phi inputs. -/
theorem actual_exact_balaban_old_new_marked_penrose
    (Pub : PublishedPenroseExtendedTwoRoot)
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
    let K : ℝ := (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
    (‖actualTwoRootInsertion U wp cp wq cq s t *
      actualExactBalabanOldRTwoRootTerm
        D j n N chi omega rootP rootQ support‖ ≤
       K * exactExtendedTwoRootTreeMajorant n N chi rootP rootQ
         support (fun X => D.oldR j X omega)) ∧
    (‖actualTwoRootInsertion U wp cp wq cq s t *
      actualExactBalabanNewRTwoRootTerm
        D j n N chi omega rootP rootQ support‖ ≤
       K * exactExtendedTwoRootTreeMajorant n N chi rootP rootQ
         support (fun X => D.newR j X omega)) := by
  dsimp
  exact ⟨
    actual_exact_extended_marked_penrose Pub n N chi rootP rootQ
      support (fun X => D.oldR j X omega)
      (fun w : ClosedLinkWalkAt (PeriodicBlock N) base =>
        actualWalkHolonomy links base w.vertices)
      wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq,
    actual_exact_extended_marked_penrose Pub n N chi rootP rootQ
      support (fun X => D.newR j X omega)
      (fun w : ClosedLinkWalkAt (PeriodicBlock N) base =>
        actualWalkHolonomy links base w.vertices)
      wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq⟩

end YMUIC.Original24
