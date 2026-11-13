import YMOriginal.Original24_ExactWeightedTreeComparison

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace YMUIC.Original24

/-!
# R7: exact published FP interface -> actual two-root criterion

The external premise is purely combinatorial: a generic
Fernandez--Procacci single-q rooted-tree exponential enumeration.
The model-facing actual two-root graph comparison is internal.
-/

/-- Exact finite-height specialization of the published
Fernández--Procacci rooted-tree exponential enumeration to an arbitrary
finite hard-core polymer system on the periodic block graph. -/
structure PublishedFPPeriodicSingleQ : Prop where
  bound :
    ∀ {Γ : Type*} [Fintype Γ]
      (N chi : ℕ)
      (rootP rootQ : Finset (PeriodicBlock N))
      (support : Γ → Finset (PeriodicBlock N))
      (z : Γ → ℂ) (d : Γ → ℕ)
      (cGeo mu lam eps : ℝ) (h : ℕ),
      1 ≤ lam → 0 < eps →
      (∑ k ∈ Finset.range (h - 2),
        actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps) ≤
      Real.exp (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity
          (fun X => (lam : ℂ) * z X) eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu h) - 1

/-- Pointwise finite-height actual two-root comparison.
Keeping this theorem explicit avoids repeatedly unfolding the large
criterion definition during elaboration. -/
theorem r7_actual_two_root_fp_bound
    (P : PublishedFPPeriodicSingleQ)
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu lam eps : ℝ) (h : ℕ)
    (hlam : 1 ≤ lam) (heps : 0 < eps) :
    (∑ k ∈ Finset.range (h - 2),
      exactExtendedTwoRootTreeMajorant
        (k + 1) N chi rootP rootQ support z *
        lam ^ (k + 1) * eps) ≤
    Real.exp (actualPeriodicFirstRootSum N chi rootP
      (actualSecondRootAugmentedSupport N support rootQ)
      (actualSecondRootAugmentedActivity
        (fun X => (lam : ℂ) * z X) eps)
      (actualSecondRootAugmentedSize d rootQ.card)
      cGeo mu h) - 1 := by
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have heps0 : 0 ≤ eps := le_of_lt heps
  have hterm :
      ∀ k : ℕ,
        exactExtendedTwoRootTreeMajorant
            (k + 1) N chi rootP rootQ support z *
            lam ^ (k + 1) * eps ≤
          actualSingleQWeightedTreeMajorant
            (k + 1) N chi rootP rootQ support z *
            lam ^ (k + 1) * eps := by
    intro k
    have htree :=
      original24_exact_two_root_weighted_tree_le_single_q
        (k + 1) N chi rootP rootQ support z
    have hpow : 0 ≤ lam ^ (k + 1) := pow_nonneg hlam0 _
    have hmul :
        exactExtendedTwoRootTreeMajorant
            (k + 1) N chi rootP rootQ support z *
            lam ^ (k + 1) ≤
          actualSingleQWeightedTreeMajorant
            (k + 1) N chi rootP rootQ support z *
            lam ^ (k + 1) :=
      mul_le_mul_of_nonneg_right htree hpow
    exact mul_le_mul_of_nonneg_right hmul heps0
  calc
    (∑ k ∈ Finset.range (h - 2),
      exactExtendedTwoRootTreeMajorant
        (k + 1) N chi rootP rootQ support z *
        lam ^ (k + 1) * eps) ≤
      ∑ k ∈ Finset.range (h - 2),
        actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps :=
        Finset.sum_le_sum (fun k hk => hterm k)
    _ ≤ Real.exp (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity
          (fun X => (lam : ℂ) * z X) eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu h) - 1 :=
      P.bound N chi rootP rootQ support z d cGeo mu lam eps h hlam heps

/-- The generic published enumeration plus the internally proved
actual graph/tree injection gives the model-facing criterion. -/
theorem r7_actual_two_root_fp_criterion
    (P : PublishedFPPeriodicSingleQ)
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu : ℝ) :
    PhysicalExactTwoRootFPCriterion
      N chi rootP rootQ support z d cGeo mu := by
  intro lam eps h hlam heps
  exact r7_actual_two_root_fp_bound P N chi rootP rootQ
    support z d cGeo mu lam eps h hlam heps

#print axioms r7_actual_two_root_fp_bound
#print axioms r7_actual_two_root_fp_criterion

end YMUIC.Original24
