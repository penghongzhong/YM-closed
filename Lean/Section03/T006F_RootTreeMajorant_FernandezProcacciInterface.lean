import Mathlib

set_option autoImplicit false

/-!
# Fernández–Procacci rooted-tree enumeration interface

External combinatorial source:
R. Fernández and A. Procacci,
"Cluster expansion for abstract polymer models. New bounds from an old approach",
Commun. Math. Phys. 274 (2007), 123–140.

Exact use boundary:
* Section 4.1, Proposition 7–8;
* equations (4.12)–(4.19);
* finite-height iterates are represented by planar rooted trees;
* permutation symmetry of child vertex-functions converts the planar-tree
  representation into labeled rooted trees with the factorial normalization;
* the finite-height sums converge monotonically to the full positive tree sum.

This file contains NO custom axiom.  The published combinatorial theorem is
passed explicitly as a structure-valued hypothesis.  The Lean theorem below
checks only the exact consequence used in the YM manuscript: a uniform bound
on every recursive finite-height sum passes to the full labeled-tree sum.
-/

namespace YMUICV128.Section03.T006F

structure FernandezProcacciRootedTreeInterface where
  finiteLabeledTreeSum : ℕ → ℝ
  recursiveRootSum : ℕ → ℝ
  fullLabeledTreeSum : ℝ
  finiteHeightIdentity :
    ∀ h, finiteLabeledTreeSum h = recursiveRootSum h
  finiteHeightNonneg :
    ∀ h, 0 ≤ finiteLabeledTreeSum h
  fullNonneg :
    0 ≤ fullLabeledTreeSum
  finiteHeightTendsto :
    Filter.Tendsto finiteLabeledTreeSum
      Filter.atTop (nhds fullLabeledTreeSum)

theorem bounded_recursive_sum_bounds_full_tree_sum
    (I : FernandezProcacciRootedTreeInterface)
    (M : ℝ)
    (hM : ∀ h, I.recursiveRootSum h ≤ M) :
    I.fullLabeledTreeSum ≤ M := by
  apply le_of_tendsto I.finiteHeightTendsto
  exact Filter.Eventually.of_forall fun h => by
    rw [I.finiteHeightIdentity h]
    exact hM h

theorem bounded_recursive_sum_bounds_full_tree_sum_nonneg
    (I : FernandezProcacciRootedTreeInterface)
    (M : ℝ)
    (hM : ∀ h, I.recursiveRootSum h ≤ M) :
    0 ≤ I.fullLabeledTreeSum ∧ I.fullLabeledTreeSum ≤ M := by
  exact ⟨I.fullNonneg,
    bounded_recursive_sum_bounds_full_tree_sum I M hM⟩

#print axioms bounded_recursive_sum_bounds_full_tree_sum
#print axioms bounded_recursive_sum_bounds_full_tree_sum_nonneg

end YMUICV128.Section03.T006F
