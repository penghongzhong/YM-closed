import Mathlib

set_option autoImplicit false

/-!
# U2 finite rooted-tree majorant — final assembly

This is the final Lean assembly for v133 `lem:root-tree-majorant`.

The only external mathematical input is the Fernández–Procacci rooted-tree
enumeration/finite-height limit interface (CMP 274 (2007), Section 4.1,
Propositions 7–8, equations (4.12)–(4.19)).

Everything else is represented by explicit hypotheses already certified by
T006A–T006E:
* every recursive finite-height root sum is <= M = N_root a_act;
* the original two-root tree family is a subfamily of the p-rooted family
  obtained by deleting the q-attachment condition.

No custom axiom is declared.
-/

namespace YMUICV128.Section03.T006G

structure FernandezProcacciRootedTreeInterface where
  finiteLabeledTreeSum : ℕ → ℝ
  recursiveRootSum : ℕ → ℝ
  fullPRootedTreeSum : ℝ
  finiteHeightIdentity :
    ∀ h, finiteLabeledTreeSum h = recursiveRootSum h
  finiteHeightNonneg :
    ∀ h, 0 ≤ finiteLabeledTreeSum h
  fullNonneg :
    0 ≤ fullPRootedTreeSum
  finiteHeightTendsto :
    Filter.Tendsto finiteLabeledTreeSum
      Filter.atTop (nhds fullPRootedTreeSum)

theorem full_p_rooted_sum_le
    (I : FernandezProcacciRootedTreeInterface)
    (M : ℝ)
    (hFinite : ∀ h, I.recursiveRootSum h ≤ M) :
    I.fullPRootedTreeSum ≤ M := by
  apply le_of_tendsto I.finiteHeightTendsto
  exact Filter.Eventually.of_forall fun h => by
    rw [I.finiteHeightIdentity h]
    exact hFinite h

theorem two_root_tree_sum_le
    (I : FernandezProcacciRootedTreeInterface)
    (twoRootTreeSum M : ℝ)
    (hTwoRootNonneg : 0 ≤ twoRootTreeSum)
    (hDomain :
      twoRootTreeSum ≤ I.fullPRootedTreeSum)
    (hFinite :
      ∀ h, I.recursiveRootSum h ≤ M) :
    0 ≤ twoRootTreeSum ∧ twoRootTreeSum ≤ M := by
  constructor
  · exact hTwoRootNonneg
  · exact hDomain.trans (full_p_rooted_sum_le I M hFinite)

theorem finite_rooted_tree_majorant
    (I : FernandezProcacciRootedTreeInterface)
    (twoRootTreeSum : ℝ)
    (Nroot : ℕ)
    (aAct : ℝ)
    (hTwoRootNonneg : 0 ≤ twoRootTreeSum)
    (hDomain :
      twoRootTreeSum ≤ I.fullPRootedTreeSum)
    (hFinite :
      ∀ h,
        I.recursiveRootSum h ≤ (Nroot : ℝ) * aAct) :
    twoRootTreeSum ≤ (Nroot : ℝ) * aAct := by
  exact (two_root_tree_sum_le
    I twoRootTreeSum ((Nroot : ℝ) * aAct)
    hTwoRootNonneg hDomain hFinite).2

#print axioms full_p_rooted_sum_le
#print axioms two_root_tree_sum_le
#print axioms finite_rooted_tree_majorant

end YMUICV128.Section03.T006G
