import YMOriginal.Original24_ExactExtendedTwoRootMayer
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# The second Wilson root can be an INTERNAL graph vertex

The original n+2-vertex connected Ursell graph is not the same
as a connected graph on only its n bulk-polymer vertices.
A second external Wilson root can have DEGREE >= 2 and connect
two bulk histories that are mutually compatible. Consequently,
deleting the second root need not produce a p-rooted tree on the
bulk graph. Any full two-root FP/KP majorant must account for this
possibility; invoking the existing one-root KP tree estimate
without an additional two-root bridge is not justified.

This source proves a structural connectivity lemma directly on
the EXACT actual extended C29 graph. It does not assert existence
of physical configurations realizing all the input root contacts.
-/

/-- An actual two-root extended graph with two bulk histories
is connected whenever root-p touches history 0 and root-q
touches BOTH histories, regardless of the contact between
the two bulk histories. Root-q is allowed to have degree 2. -/
theorem actual_two_root_extended_connected_by_q_hub
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 2 → Γ)
    (hPA : tuple 0 ∈ actualContactRoot rootP
      (fourDimPeriodicNeighborhood N chi) support)
    (hQA : tuple 0 ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support)
    (hQB : tuple 1 ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support) :
    (actualExactTwoRootGraph 2 N chi rootP rootQ support tuple).Connected := by
  let G : SimpleGraph (Sum (Fin 2) (Fin 2)) :=
    actualExactTwoRootGraph 2 N chi rootP rootQ support tuple
  have hp : G.Adj (Sum.inr (0 : Fin 2)) (Sum.inl (0 : Fin 2)) :=
    (actual_exact_rootp_bulk_edge
      2 N chi rootP rootQ support tuple 0).mpr hPA
  have hqa : G.Adj (Sum.inr (1 : Fin 2)) (Sum.inl (0 : Fin 2)) :=
    (actual_exact_rootq_bulk_edge
      2 N chi rootP rootQ support tuple 0).mpr hQA
  have hqb : G.Adj (Sum.inr (1 : Fin 2)) (Sum.inl (1 : Fin 2)) :=
    (actual_exact_rootq_bulk_edge
      2 N chi rootP rootQ support tuple 1).mpr hQB
  have hReach :
      ∀ v : Sum (Fin 2) (Fin 2),
        G.Reachable (Sum.inr (1 : Fin 2)) v := by
    intro v
    cases v with
    | inl i =>
        fin_cases i
        · exact hqa.reachable
        · exact hqb.reachable
    | inr i =>
        fin_cases i
        · exact hqa.reachable.trans hp.symm.reachable
        · exact .refl _
  exact (SimpleGraph.connected_iff_exists_forall_reachable).mpr
    ⟨Sum.inr (1 : Fin 2), hReach⟩


/-- If two physically labeled bulk polymers are mutually COMPATIBLE
while root-p touches history 0 and root-q touches both histories,
then the FULL n+2-vertex graph is connected but its bulk-only
n-vertex incompatibility graph is DISCONNECTED.

Hence deleting root-q from a full connected tree is NOT a valid
automatic reduction to the already-verified one-root U2 KP sum.
The original second-root branching is a genuine extra combinatorial
obligation, not a definitional equality. -/
theorem actual_two_root_hub_not_bulk_connected
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 2 → Γ)
    (hPA : tuple 0 ∈ actualContactRoot rootP
      (fourDimPeriodicNeighborhood N chi) support)
    (hQA : tuple 0 ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support)
    (hQB : tuple 1 ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support)
    (hAB : ¬ actualPeriodicHardCoreIncompatible N chi support
      (tuple 0) (tuple 1)) :
    (actualExactTwoRootGraph 2 N chi
      rootP rootQ support tuple).Connected ∧
    ¬(actualPeriodicLabeledHardCoreGraph 2 N chi support tuple).Connected := by
  let H : SimpleGraph (Fin 2) :=
    actualPeriodicLabeledHardCoreGraph 2 N chi support tuple
  have hNotConn : ¬ H.Connected := by
    intro h
    have hni : ¬H.IsIsolated (0 : Fin 2) :=
      h.preconnected.not_isIsolated _
    obtain ⟨v, hv⟩ :=
      (SimpleGraph.exists_adj_iff_not_isIsolated
        (G := H) (v := (0 : Fin 2))).2 hni
    fin_cases v
    · exact (H.loopless _ hv).elim
    · have hx :=
        (actual_periodic_labeled_hardcore_adj 2 N chi
          support tuple (0 : Fin 2) (1 : Fin 2)).mp hv
      exact hAB hx.2
  exact ⟨actual_two_root_extended_connected_by_q_hub
    N chi rootP rootQ support tuple hPA hQA hQB, hNotConn⟩

end YMUIC.Original24
