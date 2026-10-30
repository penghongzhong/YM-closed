import YMOriginal.Original24_ExactTreeCount
import YMOriginal.Original24_ExactRealTwoRootFPSeries

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-- The positive SINGLE-q physical tree majorant on actual finite
four-dimensional periodic polymer supports, with the original
n! symmetry factor and SAME underlying old/new R activity z. -/
def actualSingleQWeightedTreeMajorant
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) : ℝ := by
  classical
  exact (Nat.factorial n : ℝ)⁻¹ *
    ∑ tuple : Fin n → Γ,
      ((actualSingleQSpanningTrees n N chi rootP rootQ
        support tuple).card : ℝ) *
        ∏ i : Fin n, ‖z (tuple i)‖

/-- The EXACT original physical n+2-vertex two-root Mayer spanning-tree
sum is bounded by its one-q positive rooted hard-core majorant,
with NO change of source coefficients, no lost factorial, and q
allowed arbitrary branching. All summands are actual finite
labeled graph/tree objects, not abstract scalar surrogate trees.

The separate FP tree exponential enumeration and the actual
CMP119/CMP122 native-history identification still need proof. -/
theorem original24_exact_two_root_weighted_tree_le_single_q
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    exactExtendedTwoRootTreeMajorant n N chi
      rootP rootQ support z ≤
    actualSingleQWeightedTreeMajorant n N chi
      rootP rootQ support z := by
  classical
  have hpoint (tuple : Fin n → Γ) :
      (if (actualExactTwoRootGraph n N chi
        rootP rootQ support tuple).Connected then
          ((exactExtendedSpanningTrees n
             (actualExactTwoRootGraph n N chi
               rootP rootQ support tuple)).card : ℝ) *
            ∏ i : Fin n, ‖z (tuple i)‖
        else 0) ≤
      ((actualSingleQSpanningTrees n N chi rootP rootQ
        support tuple).card : ℝ) *
        ∏ i : Fin n, ‖z (tuple i)‖ := by
    have hprod : 0 ≤ ∏ i : Fin n, ‖z (tuple i)‖ :=
      Finset.prod_nonneg (fun i _ => norm_nonneg _)
    by_cases hc : (actualExactTwoRootGraph n N chi
      rootP rootQ support tuple).Connected
    · simp only [hc, ite_true]
      have hcard : ((exactExtendedSpanningTrees n
          (actualExactTwoRootGraph n N chi
            rootP rootQ support tuple)).card : ℝ) ≤
          ((actualSingleQSpanningTrees n N chi
            rootP rootQ support tuple).card : ℝ) :=
        Nat.cast_le.mpr
          (original24_exact_tree_count_le_single_q
            n N chi rootP rootQ support tuple)
      exact mul_le_mul_of_nonneg_right hcard hprod
    · simp only [hc, ite_false]
      exact mul_nonneg (Nat.cast_nonneg _) hprod
  have hsum :
      (∑ tuple : Fin n → Γ,
        if (actualExactTwoRootGraph n N chi
          rootP rootQ support tuple).Connected then
          ((exactExtendedSpanningTrees n
            (actualExactTwoRootGraph n N chi
              rootP rootQ support tuple)).card : ℝ) *
            ∏ i : Fin n, ‖z (tuple i)‖
        else 0) ≤
      ∑ tuple : Fin n → Γ,
        ((actualSingleQSpanningTrees n N chi
          rootP rootQ support tuple).card : ℝ) *
          ∏ i : Fin n, ‖z (tuple i)‖ :=
    Finset.sum_le_sum (fun tuple _ => hpoint tuple)
  unfold exactExtendedTwoRootTreeMajorant actualSingleQWeightedTreeMajorant
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end YMUIC.Original24
