import YMOriginal.Original24_ExactWeightedTreeComparison

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# R7: exact published FP interface -> actual two-root criterion

The external premise below is deliberately model-independent in the
sense relevant to Fernandez--Procacci: it is a rooted hard-core
single-q positive-tree enumeration on arbitrary finite polymer
species.  It does NOT mention Bałaban histories, Yang--Mills
couplings, Wilson observables, or the desired connected Mayer sum.

The actual two-root Wilson graph is mapped to this generic single-q
system by already kernel-proved graph/tree transport, and the exact
1/n! normalization is internal.
-/

/-- Exact finite-height specialization of the published
Fernández--Procacci rooted-tree exponential enumeration to an arbitrary
finite hard-core polymer system on the periodic block graph.

This is an EXTERNAL COMBINATORIAL interface, analogous to the existing
published Penrose interface; it is not a model theorem. -/
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

/-- The published generic single-q enumeration plus the internally
proved exact graph-to-single-q tree injection yields the precise
model-facing finite-height criterion previously left as hFP.

No Yang--Mills activity estimate, source analyticity, or final connected
series bound is an assumption of this theorem. -/
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
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have heps0 : 0 ≤ eps := le_of_lt heps
  calc
    (∑ k ∈ Finset.range (h - 2),
      exactExtendedTwoRootTreeMajorant
        (k + 1) N chi rootP rootQ support z *
        lam ^ (k + 1) * eps) ≤
      ∑ k ∈ Finset.range (h - 2),
        actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps := by
        apply Finset.sum_le_sum
        intro k hk
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
    _ ≤ Real.exp (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity
          (fun X => (lam : ℂ) * z X) eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu h) - 1 :=
      P.bound N chi rootP rootQ support z d cGeo mu lam eps h hlam heps

#print axioms r7_actual_two_root_fp_criterion

end YMUIC.Original24
