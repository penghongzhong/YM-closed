import YMOriginal.Original24_FPFirstGraph
import YMOriginal.Original24_PublishedPenroseExtended
import Mathlib.Combinatorics.SimpleGraph.Star

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section

namespace YMUIC.Original24

/-!
# Exact n=1 C29 double-root Mayer/Ursell coefficient without Penrose or FP

For ONE native bulk history X, the only allowed connected physical
graph has vertices p-X-q and NO p-q edge. This is the three-vertex
star graph centered on X, with two edges. Consequently its exact
connected graph sum is (-1)^2 = +1. Without a bridge, the coefficient
vanishes by disconnection.

The result is the ACTUAL source graph's first connected Mayer
coefficient, not an abstract conditional rooted coefficient.
Neither the external PublishedPenroseExtendedTwoRoot theorem, the
all-order PhysicalExactTwoRootFPCriterion, an assumed connected
coefficient, nor the eventual B11 source-class conclusion is a
theorem parameter.
-/

/-- A finite tree has precisely one connected spanning subgraph
(among the subgraphs of itself), hence its hard-core connected
alternating Mayer graph sum equals (-1)^|edges|.

This is a structural finite-graph identity with no external
Penrose theorem premise. -/
theorem original24_exact_connected_graph_sum_of_tree
    (n : ℕ) (G : SimpleGraph (Sum (Fin n) (Fin 2)))
    [Fintype G.edgeSet] (hG : G.IsTree) :
    exactExtendedConnectedGraphSum n G =
      (-1 : ℝ) ^ G.edgeFinset.card := by
  classical
  have hMin : Minimal SimpleGraph.Connected G :=
    SimpleGraph.isTree_iff_minimal_connected.mp hG
  have hOnly (H : SimpleGraph (Sum (Fin n) (Fin 2)))
      (hHG : H ≤ G) (hHC : H.Connected) : H = G :=
    le_antisymm hHG (hMin.2 hHC hHG)
  unfold exactExtendedConnectedGraphSum
  rw [Finset.sum_eq_single G]
  · have hroot : G ≤ G ∧ G.Connected := ⟨le_rfl, hG.connected⟩
    simp only [hroot, true_and, ite_true, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card]
  · intro H _ hne
    have hno : ¬(H ≤ G ∧ H.Connected) := by
      intro hh
      exact hne (hOnly H hh.1 hh.2)
    simp [hno]
  · intro hg
    exact (hg (Finset.mem_univ G)).elim

/-- On the true physical three-vertex double-Wilson-root graph, a
polymer X touching both p and q makes the graph *definitionally*
a star after the exact contact rewrite (not a bulk-only graph). -/
theorem original24_actual_one_bulk_graph_eq_star
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 1 → Γ)
    (hp : tuple 0 ∈ actualContactRoot rootP
      (fourDimPeriodicNeighborhood N chi) support)
    (hq : tuple 0 ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support) :
    actualExactTwoRootGraph 1 N chi rootP rootQ support tuple =
      SimpleGraph.starGraph (Sum.inl (0 : Fin 1)) := by
  classical
  ext u v
  cases u with
  | inl i =>
      fin_cases i
      cases v with
      | inl j =>
          fin_cases j
          simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
            SimpleGraph.fromRel_adj]
      | inr j =>
          fin_cases j <;>
            simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
              SimpleGraph.fromRel_adj, hp, hq]
  | inr i =>
      fin_cases i
      · cases v with
        | inl j =>
            fin_cases j
            simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
              SimpleGraph.fromRel_adj, hp, hq]
        | inr j =>
            fin_cases j <;>
              simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
                SimpleGraph.fromRel_adj]
      · cases v with
        | inl j =>
            fin_cases j
            simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
              SimpleGraph.fromRel_adj, hp, hq]
        | inr j =>
            fin_cases j <;>
              simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
                SimpleGraph.fromRel_adj]

open Classical in
/-- **The exact original n=1 Mayer/Ursell coefficient:** +1 if
the one bulk history contacts BOTH Wilson roots, zero otherwise.
No Penrose, no FP, no artificial abstract coefficient or axiom. -/
theorem original24_exact_one_bulk_ursell_eq_bridge_indicator
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 1 → Γ) :
    actualExactTwoRootUrsellCoefficient 1 N chi
      rootP rootQ support tuple =
        if tuple 0 ∈ actualOnePolymerTwoRootBridge
          N chi rootP rootQ support then 1 else 0 := by
  classical
  by_cases hbridge :
      tuple 0 ∈ actualOnePolymerTwoRootBridge
        N chi rootP rootQ support
  · have hp :
        tuple 0 ∈ actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi) support :=
      (Finset.mem_inter.mp hbridge).1
    have hq :
        tuple 0 ∈ actualContactRoot rootQ
          (fourDimPeriodicNeighborhood N chi) support :=
      (Finset.mem_inter.mp hbridge).2
    have hGraph :=
      original24_actual_one_bulk_graph_eq_star
        N chi rootP rootQ support tuple hp hq
    have hTree :
        (SimpleGraph.starGraph
          (Sum.inl (0 : Fin 1) :
            Sum (Fin 1) (Fin 2))).IsTree :=
      SimpleGraph.isTree_starGraph _
    have hCard :
        (SimpleGraph.starGraph
          (Sum.inl (0 : Fin 1) :
            Sum (Fin 1) (Fin 2))).edgeFinset.card = 2 := by
      have h := hTree.card_edgeFinset
      have hThree :
          Fintype.card (Sum (Fin 1) (Fin 2)) = 3 := by
        decide
      omega
    rw [actual_exact_extended_ursell_eq_graph_sum, hGraph]
    rw [original24_exact_connected_graph_sum_of_tree 1 _ hTree, hCard]
    simp [hbridge]
  · have hDisc :
        ¬(actualExactTwoRootGraph 1 N chi
          rootP rootQ support tuple).Connected := by
      intro hc
      exact hbridge
        ((original24_exact_one_bulk_graph_connected_iff
          N chi rootP rootQ support tuple).mp hc)
    have hZero := actual_exact_two_root_ursell_zero_of_disconnected
      1 N chi rootP rootQ support tuple hDisc
    simpa [hbridge] using hZero

end YMUIC.Original24
