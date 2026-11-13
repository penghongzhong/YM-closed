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

/-- The published single-q enumeration plus the internally proved exact
physical graph embedding yields the formerly separate physical
two-root FP criterion. -/
set_option maxHeartbeats 800000 in
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
      N chi rootP rootQ support z d cGeo mu := by
  intro lam eps h hlam heps
  have hterm : ∀ k ∈ Finset.range (h - 2),
      exactExtendedTwoRootTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps ≤
      actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps := by
    intro k hk
    have htree :=
      original24_exact_two_root_weighted_tree_le_single_q
        (k + 1) N chi rootP rootQ support z
    have hfactor : 0 ≤ lam ^ (k + 1) * eps := by
      exact mul_nonneg (pow_nonneg (by linarith) _) heps.le
    calc
      exactExtendedTwoRootTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps =
        exactExtendedTwoRootTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          (lam ^ (k + 1) * eps) := by ring
      _ ≤ actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          (lam ^ (k + 1) * eps) :=
        mul_le_mul_of_nonneg_right htree hfactor
      _ = actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps := by ring
  calc
    (∑ k ∈ Finset.range (h - 2),
      exactExtendedTwoRootTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps) ≤
      ∑ k ∈ Finset.range (h - 2),
        actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps := by
        exact Finset.sum_le_sum hterm
    _ ≤ Real.exp
        (actualPeriodicFirstRootSum N chi rootP
          (actualSecondRootAugmentedSupport N support rootQ)
          (actualSecondRootAugmentedActivity
            (fun X => (lam : ℂ) * z X) eps)
          (actualSecondRootAugmentedSize d rootQ.card)
          cGeo mu h) - 1 :=
      FP.finiteHeightBound N chi rootP rootQ support z d
        cGeo mu lam eps h hgeom hlam heps

end YMUIC.Original24
