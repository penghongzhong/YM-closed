import YMOriginal.Original24_ExactWeightedTreeComparison
import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Published Fernández--Procacci single-q enumeration interface

This is the exact external combinatorial use boundary needed after the
internal physical graph dictionary has already been proved.

The external statement is deliberately NOT the target two-root Yang--Mills
bound. It concerns the positive p-rooted tree family after q has been
adjoined as one distinguished polymer species. The internally proved
exact two-root weighted-tree comparison maps the literal C29 n+2-vertex
physical graph into this family.

The factor lam^n * eps marks n ordinary bulk vertices and exactly one q
vertex. The recursive right-hand side is the already kernel-checked
finite-height KP recursion. The sign condition 0 <= cGeo * mu is explicit.
-/

/-- Universal published rooted-tree enumeration, specialized only to the
finite single-q hard-core model. This is a typed external theorem
interface, not a custom axiom and not a Yang--Mills analytic estimate. -/
structure PublishedFernandezProcacciSingleQ : Prop where
  finiteHeightBound :
    ∀ {Γ : Type*} [Fintype Γ]
      (N chi : ℕ)
      (rootP rootQ : Finset (PeriodicBlock N))
      (support : Γ → Finset (PeriodicBlock N))
      (z : Γ → ℂ) (d : Γ → ℕ)
      (cGeo mu lam eps : ℝ) (h : ℕ),
      0 ≤ cGeo * mu →
      1 ≤ lam →
      0 < eps →
      (∑ k ∈ Finset.range (h - 2),
        actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps) ≤
      Real.exp
        (actualPeriodicFirstRootSum N chi rootP
          (actualSecondRootAugmentedSupport N support rootQ)
          (actualSecondRootAugmentedActivity
            (fun X => (lam : ℂ) * z X) eps)
          (actualSecondRootAugmentedSize d rootQ.card)
          cGeo mu h) - 1

/-- Pointwise weighted comparison after the exact physical graph
embedding.  Keeping this as a separate lemma avoids repeatedly unfolding
the full physical FP criterion during the finite-sum proof. -/
theorem published_single_q_weighted_term
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (lam eps : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps)
    (n : ℕ) :
    exactExtendedTwoRootTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps ≤
      actualSingleQWeightedTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps := by
  have htree :=
    original24_exact_two_root_weighted_tree_le_single_q
      n N chi rootP rootQ support z
  have hfactor : 0 ≤ lam ^ n * eps :=
    mul_nonneg (pow_nonneg hlam _) heps
  calc
    exactExtendedTwoRootTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps =
      exactExtendedTwoRootTreeMajorant
        n N chi rootP rootQ support z * (lam ^ n * eps) := by
          ring
    _ ≤ actualSingleQWeightedTreeMajorant
        n N chi rootP rootQ support z * (lam ^ n * eps) :=
      mul_le_mul_of_nonneg_right htree hfactor
    _ = actualSingleQWeightedTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps := by
          ring

/-- Finite-height physical two-root tree sum is bounded by the
corresponding positive single-q sum. -/
theorem published_single_q_weighted_sum
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (lam eps : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps)
    (h : ℕ) :
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
  exact published_single_q_weighted_term
    N chi rootP rootQ support z lam eps hlam heps (k + 1)

/-- Fully explicit physical FP inequality, avoiding any unfolding of the
named criterion during the main proof. -/
theorem published_single_q_explicit_physical_FP
    (FP : PublishedFernandezProcacciSingleQ)
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu : ℝ)
    (hgeom : 0 ≤ cGeo * mu) :
    ∀ lam eps : ℝ, ∀ h : ℕ, 1 ≤ lam → 0 < eps →
      (∑ k ∈ Finset.range (h - 2),
        exactExtendedTwoRootTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps) ≤
      Real.exp
        (actualPeriodicFirstRootSum N chi rootP
          (actualSecondRootAugmentedSupport N support rootQ)
          (actualSecondRootAugmentedActivity
            (fun X => (lam : ℂ) * z X) eps)
          (actualSecondRootAugmentedSize d rootQ.card)
          cGeo mu h) - 1 := by
  intro lam eps h hlam heps
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have heps0 : 0 ≤ eps := heps.le
  exact
    (published_single_q_weighted_sum
      N chi rootP rootQ support z lam eps hlam0 heps0 h).trans
      (FP.finiteHeightBound N chi rootP rootQ support z d
        cGeo mu lam eps h hgeom hlam heps)

/-- The explicit theorem is definitionally the previously used named
physical criterion.  This wrapper contains no unfolding tactic. -/
theorem physicalExactTwoRootFPCriterion_of_published
    (FP : PublishedFernandezProcacciSingleQ)
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu : ℝ)
    (hgeom : 0 ≤ cGeo * mu) :
    PhysicalExactTwoRootFPCriterion
      N chi rootP rootQ support z d cGeo mu :=
  published_single_q_explicit_physical_FP
    FP N chi rootP rootQ support z d cGeo mu hgeom

#print axioms published_single_q_weighted_term
#print axioms published_single_q_weighted_sum
#print axioms published_single_q_explicit_physical_FP
#print axioms physicalExactTwoRootFPCriterion_of_published

end YMUIC.Original24
