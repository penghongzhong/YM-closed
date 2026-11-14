import YMOriginal.Original24_PeriodicRootTreeLimit
import YMOriginal.Original24_TwoRootFullRadius
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24 terminal Ursell--Penrose/FP bridge on actual periodic 4D polymers

All finite-height KP first-root bounds are derived by the strict
Original24_PeriodicRootTreeLimit module from the original unmarked
per-block U1 activity and exact physical periodic neighborhoods.

The two separate EXTERNAL combinatorial conditions are:
(1) pointwise hard-core Penrose tree domination for connected
    Ursell coefficients Phi_n (hPenrose),
(2) Fernández--Procacci labeled-tree/factorial enumeration comparing
    the truncated labeled sums with the physical finite-height
    periodic KP recursion (hFP).

We DO NOT declare either as an axiom, and DO NOT claim that arbitrary
complex Phi_n comes from actual Balaban R histories.  The precise
connected-history-to-periodic-polymer dictionary, and the same
fixed-D counterterm/source normalization, are still actual YM model
obligations. Crucially, absolute convergence and the full connected
sum bound are PROVED, not supplied as hypotheses.
-/

/-- A physical 4D periodic U1 polymer model plus the two PUBLISHED
combinatorial interfaces implies absolute convergence of the complete
infinite connected Ursell cluster series.  The full-sum estimate
is derived from finite prefixes, so no convergence or full tree
norm bound is included among the inputs. -/
theorem original24_connected_ursell_from_periodic_FP
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct)
    (Phi : ℕ → ℂ)
    (labeledTree : ℕ → ℝ)
    (hPenrose : ∀ n, ‖Phi n‖ ≤ labeledTree n)
    (hFP : ∀ n,
      (∑ k ∈ Finset.range n, labeledTree k) ≤
        actualPeriodicFirstRootSum N chi root support z d cGeo mu n) :
    Summable Phi ∧
    Summable (fun n => ‖Phi n‖) ∧
    (∑' n, ‖Phi n‖) ≤
      ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ)) * aAct := by
  have hroot : ∀ n,
      actualPeriodicFirstRootSum N chi root support z d cGeo mu n ≤
        ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct :=
    actual_periodic_first_root_uniform N chi root support z d
      kappa mu cGeo aAct ha hdelta hsize hsmall hLocalNorm
  have hpref (n : ℕ) :
      (∑ k ∈ Finset.range n, ‖Phi k‖) ≤
        ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, labeledTree k :=
        Finset.sum_le_sum (fun k hk => hPenrose k)
      _ ≤ actualPeriodicFirstRootSum
        N chi root support z d cGeo mu n := hFP n
      _ ≤ _ := hroot n
  have hsNorm : Summable (fun n => ‖Phi n‖) :=
    summable_of_sum_range_le (fun n => norm_nonneg (Phi n)) hpref
  have hs : Summable Phi := summable_norm_iff.mp hsNorm
  exact ⟨hs, hsNorm, hsNorm.tsum_le_of_sum_range_le hpref⟩

/-- Actual bounded two-root SU(2) source insertions now act on the
COMPLETE connected Ursell series, with both convergence and a
cutoff/volume-independent first-root factor derived from U1/KP.
The sole external combinatorial inputs are separated hPenrose/hFP;
the desired full cluster estimate is not a premise. -/
theorem original24_actual_two_root_connected_ursell
    {P T S Γ : Type*} [Fintype T] [Fintype S] [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct)
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (Phi : ℕ → ℂ)
    (labeledTree : ℕ → ℝ)
    (hPenrose : ∀ n, ‖Phi n‖ ≤ labeledTree n)
    (hFP : ∀ n,
      (∑ k ∈ Finset.range n, labeledTree k) ≤
        actualPeriodicFirstRootSum N chi root support z d cGeo mu n) :
    Summable (fun n => actualTwoRootInsertion U wp cp wq cq s t * Phi n) ∧
    (∑' n, ‖actualTwoRootInsertion U wp cp wq cq s t * Phi n‖) ≤
      ((Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)) *
        (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct) := by
  let D : ℂ := actualTwoRootInsertion U wp cp wq cq s t
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
  let M : ℝ :=
    ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (root.card : ℝ)) * aAct
  have hKp : 0 ≤ Real.exp (radius * Bp) - 1 := by
    exact sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hKq : 0 ≤ Real.exp (radius * Bq) - 1 := by
    exact sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hKp hKq
  have hD : ‖D‖ ≤ K :=
    actual_two_root_insertion_full_radius U wp cp wq cq
      s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  obtain ⟨hPhi, hNorm, hTotal⟩ :=
    original24_connected_ursell_from_periodic_FP
      N chi root support z d kappa mu cGeo aAct ha hdelta
      hsize hsmall hLocalNorm Phi labeledTree hPenrose hFP
  have hMarkedNorm :
      Summable (fun n => ‖D * Phi n‖) := by
    simpa only [norm_mul] using hNorm.mul_left ‖D‖
  have hBound :
      (∑' n, ‖D * Phi n‖) ≤ K * M := by
    calc
      (∑' n, ‖D * Phi n‖) =
          ‖D‖ * (∑' n, ‖Phi n‖) := by
        simp only [norm_mul, tsum_mul_left]
      _ ≤ K * (∑' n, ‖Phi n‖) :=
        mul_le_mul_of_nonneg_right hD
          (tsum_nonneg (fun n => norm_nonneg _))
      _ ≤ K * M := mul_le_mul_of_nonneg_left hTotal hK
  have hMarked : Summable (fun n => D * Phi n) :=
    summable_norm_iff.mp hMarkedNorm
  exact ⟨hMarked, hBound⟩

end YMUIC.Original24
