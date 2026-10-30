import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# A rigorously valid second-external-root marking device

The original unmarked source-root tree recursion cannot simply
discard its second external root: on K_{2,2}, the full two-root graph
has four trees while the p-only source graph has one.

The correct formal fugacity device introduces one DUMMY polymer species
q with activity eps, and counts the q-species among AUGMENTED rooted
trees. Trees with EXACTLY ONE q then contribute eps times their
original positive tree weight. Their sum is bounded by the complete
augmented-rooted-tree sum (which also allows 0 or >=2 q copies).

The combinatorial identity between these exactly-one-q trees and
the manuscript's n+2-vertex trees with the correct 1/n! remains to
be formally established. This module proves the positive-term
coefficient extraction without assuming any such identity.
-/

/-- Nonnegative weighted first fugacity coefficient is bounded by the
entire nonnegative polynomial/tree sum, at any eps >= 0. -/
theorem one_marked_species_fugacity_le_full_tree
    {Tree : Type*} [DecidableEq Tree]
    (trees : Finset Tree)
    (markedCount : Tree → ℕ) (weight : Tree → ℝ)
    (hweight : ∀ T, 0 ≤ weight T)
    (eps : ℝ) (heps : 0 ≤ eps) :
    eps * (∑ T ∈ trees.filter (fun T => markedCount T = 1),
      weight T) ≤
    ∑ T ∈ trees, weight T * eps ^ markedCount T := by
  classical
  let marked : Finset Tree := trees.filter (fun T => markedCount T = 1)
  have hsubset : marked ⊆ trees := Finset.filter_subset _ _
  have hnonneg (T : Tree) :
      0 ≤ weight T * eps ^ markedCount T :=
    mul_nonneg (hweight T) (pow_nonneg heps _)
  have hs :
      (∑ T ∈ marked, weight T * eps ^ markedCount T) ≤
        ∑ T ∈ trees, weight T * eps ^ markedCount T :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun T _ _ => hnonneg T)
  calc
    eps * (∑ T ∈ marked, weight T) =
        ∑ T ∈ marked, weight T * eps ^ markedCount T := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      have hEq : markedCount T = 1 := (Finset.mem_filter.mp hT).2
      simp only [hEq, pow_one]
      ring
    _ ≤ ∑ T ∈ trees, weight T * eps ^ markedCount T := hs

/-- If eps > 0, the one-q marked subseries is bounded by the
complete doped tree sum divided by eps, not by the UNMARKED
single-root tree sum. This division is the correct price of
marking the second external root. -/
theorem one_marked_species_from_doped_majorant
    {Tree : Type*} [DecidableEq Tree]
    (trees : Finset Tree)
    (markedCount : Tree → ℕ) (weight : Tree → ℝ)
    (hweight : ∀ T, 0 ≤ weight T)
    (eps M : ℝ) (heps : 0 < eps)
    (hfull :
      (∑ T ∈ trees, weight T * eps ^ markedCount T) ≤ M) :
    (∑ T ∈ trees.filter (fun T => markedCount T = 1),
      weight T) ≤ M / eps := by
  apply (le_div_iff₀ heps).mpr
  have hCoeff :=
    one_marked_species_fugacity_le_full_tree
      trees markedCount weight hweight eps heps.le
  exact hCoeff.trans hfull

end YMUIC.Original24
