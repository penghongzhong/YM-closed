import YMOriginal.Original24_ExactExtendedTwoRootMayer
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Two-root extended Ursell graph: exact external-root attachment

The exact C29 extended graph has n labeled bulk vertices and TWO
distinct Wilson roots, with no direct root-to-root bond.  Here
we derive, directly from connectedness of the full graph, that EACH
external root must be adjacent to some ACTUAL bulk polymer.

In particular: n=0 gives a zero two-root cumulant; and if the
physical source root is not touched by any bulk polymer, the
coefficient vanishes for ALL n.  This prevents an impossible n=0
Mayer source term and avoids assuming arbitrary Phi_n.
-/

/-- Connectedness of the full extended n+2-vertex C29 graph
forces a real, physical bulk attachment to EACH external Wilson
root, not merely an arbitrary abstract graph connection. -/
theorem actual_exact_connected_has_two_root_contacts
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ)
    (hc : (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Connected) :
    (∃ i : Fin n,
      tuple i ∈ actualContactRoot rootP
        (fourDimPeriodicNeighborhood N chi) support) ∧
    (∃ i : Fin n,
      tuple i ∈ actualContactRoot rootQ
        (fourDimPeriodicNeighborhood N chi) support) := by
  let G : SimpleGraph (Sum (Fin n) (Fin 2)) :=
    actualExactTwoRootGraph n N chi rootP rootQ support tuple
  have hP : ¬ G.IsIsolated (Sum.inr (0 : Fin 2)) :=
    hc.preconnected.not_isIsolated _
  have hQ : ¬ G.IsIsolated (Sum.inr (1 : Fin 2)) :=
    hc.preconnected.not_isIsolated _
  obtain ⟨vP, hvP⟩ :=
    (SimpleGraph.exists_adj_iff_not_isIsolated
      (G := G) (v := Sum.inr (0 : Fin 2))).2 hP
  obtain ⟨vQ, hvQ⟩ :=
    (SimpleGraph.exists_adj_iff_not_isIsolated
      (G := G) (v := Sum.inr (1 : Fin 2))).2 hQ
  have hpcontact :
      ∃ i : Fin n,
        tuple i ∈ actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi) support := by
    cases vP with
    | inl i =>
        refine ⟨i, ?_⟩
        exact (actual_exact_rootp_bulk_edge
          n N chi rootP rootQ support tuple i).mp hvP
    | inr j =>
        have hNo :
            ¬G.Adj (Sum.inr (0 : Fin 2)) (Sum.inr j) := by
          simp [G, actualExactTwoRootGraph, actualExactTwoRootRelation,
            SimpleGraph.fromRel_adj]
        exact (hNo hvP).elim
  have hqcontact :
      ∃ i : Fin n,
        tuple i ∈ actualContactRoot rootQ
          (fourDimPeriodicNeighborhood N chi) support := by
    cases vQ with
    | inl i =>
        refine ⟨i, ?_⟩
        exact (actual_exact_rootq_bulk_edge
          n N chi rootP rootQ support tuple i).mp hvQ
    | inr j =>
        have hNo :
            ¬G.Adj (Sum.inr (1 : Fin 2)) (Sum.inr j) := by
          simp [G, actualExactTwoRootGraph, actualExactTwoRootRelation,
            SimpleGraph.fromRel_adj]
        exact (hNo hvQ).elim
  exact ⟨hpcontact, hqcontact⟩

/-- Full extended hard-core graph cannot be connected when it has
zero bulk vertices: the two Wilson roots have no direct edge. -/
theorem actual_exact_two_root_graph_zero_bulk_disconnected
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 0 → Γ) :
    ¬ (actualExactTwoRootGraph 0 N chi rootP rootQ support tuple).Connected := by
  intro hconn
  obtain ⟨i, _⟩ :=
    (actual_exact_connected_has_two_root_contacts
      0 N chi rootP rootQ support tuple hconn).1
  exact i.elim0

/-- For arbitrary actual U1 old/new-R activities, the n=0
TWO-root Mayer term vanishes; it cannot be counted as a
disconnected or vacuum cluster. -/
theorem actual_exact_two_root_mayer_zero_bulk
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    actualExactTwoRootMayerTerm 0 N chi rootP rootQ support z = 0 := by
  classical
  unfold actualExactTwoRootMayerTerm
  have hzero (tuple : Fin 0 → Γ) :
      ¬ (actualExactTwoRootGraph 0 N chi rootP rootQ
        support tuple).Connected :=
    actual_exact_two_root_graph_zero_bulk_disconnected
      N chi rootP rootQ support tuple
  simp [hzero]

/-- No physical root-P attachments implies zero exact two-root
Mayer term at EVERY order; this is a necessary connectedness
property of the ACTUAL extended graph. -/
theorem actual_exact_two_root_mayer_zero_without_p_contact
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (hp : actualContactRoot rootP
      (fourDimPeriodicNeighborhood N chi) support = ∅) :
    actualExactTwoRootMayerTerm n N chi rootP rootQ support z = 0 := by
  classical
  unfold actualExactTwoRootMayerTerm
  have hDisc (tuple : Fin n → Γ) :
      ¬(actualExactTwoRootGraph n N chi rootP rootQ
        support tuple).Connected := by
    intro hc
    obtain ⟨i, hi⟩ :=
      (actual_exact_connected_has_two_root_contacts
        n N chi rootP rootQ support tuple hc).1
    rw [hp] at hi
    simp at hi
  simp [hDisc]

end YMUIC.Original24
