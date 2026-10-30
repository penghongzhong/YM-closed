import YMOriginal.Original24_FPFirstConnectedBulk
import YMOriginal.Original24_ExactExtendedTwoRootMayer
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-- The n=1 term of the ACTUAL two-root extended Mayer graph is
connected exactly when its one bulk history meets BOTH physical
external Wilson root supports.  The second root may be a hub at
higher orders; this lemma isolates the first nonzero coefficient.

No abstract graph or assumed connectedness-to-source dictionary. -/
theorem original24_exact_one_bulk_graph_connected_iff
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 1 → Γ) :
    (actualExactTwoRootGraph 1 N chi
      rootP rootQ support tuple).Connected ↔
    tuple 0 ∈ actualOnePolymerTwoRootBridge
      N chi rootP rootQ support := by
  classical
  let G := actualExactTwoRootGraph 1 N chi rootP rootQ support tuple
  constructor
  · intro hconn
    obtain ⟨⟨i, hp⟩, ⟨j, hq⟩⟩ :=
      actual_exact_connected_has_two_root_contacts
        1 N chi rootP rootQ support tuple hconn
    have hip : i = 0 := Subsingleton.elim _ _
    have hiq : j = 0 := Subsingleton.elim _ _
    rw [hip] at hp
    rw [hiq] at hq
    exact Finset.mem_inter.mpr ⟨hp, hq⟩
  · intro hcontact
    have hp :
        tuple 0 ∈ actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi) support :=
      (Finset.mem_inter.mp hcontact).1
    have hq :
        tuple 0 ∈ actualContactRoot rootQ
          (fourDimPeriodicNeighborhood N chi) support :=
      (Finset.mem_inter.mp hcontact).2
    have hep : G.Adj (Sum.inr (0 : Fin 2)) (Sum.inl (0 : Fin 1)) :=
      (actual_exact_rootp_bulk_edge
        1 N chi rootP rootQ support tuple 0).mpr hp
    have heq : G.Adj (Sum.inr (1 : Fin 2)) (Sum.inl (0 : Fin 1)) :=
      (actual_exact_rootq_bulk_edge
        1 N chi rootP rootQ support tuple 0).mpr hq
    have hreach :
        ∀ v : Sum (Fin 1) (Fin 2),
          G.Reachable (Sum.inl (0 : Fin 1)) v := by
      intro v
      cases v with
      | inl i =>
          fin_cases i
          exact .refl _
      | inr i =>
          fin_cases i
          · exact hep.symm.reachable
          · exact heq.symm.reachable
    exact (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
      ⟨Sum.inl (0 : Fin 1), hreach⟩

end YMUIC.Original24
