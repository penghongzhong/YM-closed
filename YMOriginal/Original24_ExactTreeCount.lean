import YMOriginal.Original24_ExactTreeTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-- The actual augmented physical p-rooted, q-species spanning-tree set.
A possible extra direct p-q contact only increases the positive majorant. -/
def actualSingleQSpanningTrees
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    Finset (SimpleGraph (Sum (Sum (Fin n) Unit) Unit)) := by
  classical
  exact Finset.univ.filter (fun T =>
    T ≤ actualSingleQRootGraph n N chi rootP rootQ support tuple ∧ T.IsTree)

/-- Exact physical original two-root Mayer spanning-tree count is bounded
by the SINGLE-q augmented p-rooted hard-core tree count.
This removes any separate unproved tree cardinality assumption.

The matching label/fugacity coefficient and all-height FP exponential
summation remain separate, explicitly unproved analytic/combinatorial
steps; this theorem contains neither as a parameter. -/
theorem original24_exact_tree_count_le_single_q
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    (exactExtendedSpanningTrees n
      (actualExactTwoRootGraph n N chi rootP rootQ support tuple)).card ≤
    (actualSingleQSpanningTrees n N chi rootP rootQ support tuple).card := by
  classical
  let e : Sum (Fin n) (Fin 2) ≃ Sum (Sum (Fin n) Unit) Unit :=
    twoRootToSingleQ n
  let oldTrees := exactExtendedSpanningTrees n
    (actualExactTwoRootGraph n N chi rootP rootQ support tuple)
  let newTrees := actualSingleQSpanningTrees n N chi rootP rootQ support tuple
  let f : SimpleGraph (Sum (Fin n) (Fin 2)) →
      SimpleGraph (Sum (Sum (Fin n) Unit) Unit) :=
    fun T => SimpleGraph.comap e.symm T
  have hmap (T : SimpleGraph (Sum (Fin n) (Fin 2)))
      (hT : T ∈ oldTrees) : f T ∈ newTrees := by
    obtain ⟨T', hTtree, hTsub, hAdj⟩ :=
      original24_exact_spanning_tree_to_single_q
        n N chi rootP rootQ support tuple T hT
    have hEq : f T = T' := by
      ext x y
      have hp := (hAdj (e.symm x) (e.symm y)).symm
      simpa [f, e, SimpleGraph.comap_adj] using hp
    change f T ∈ (Finset.univ : Finset
      (SimpleGraph (Sum (Sum (Fin n) Unit) Unit))).filter
      (fun S => S ≤ actualSingleQRootGraph n N chi rootP rootQ support tuple ∧
        S.IsTree)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by rw [hEq]; exact ⟨hTsub, hTtree⟩⟩
  let fSubtype : {T // T ∈ oldTrees} → {S // S ∈ newTrees} :=
    fun T => ⟨f T.val, hmap T.val T.property⟩
  have hinj : Function.Injective fSubtype := by
    intro T1 T2 h
    apply Subtype.ext
    have heq : f T1.val = f T2.val := congrArg Subtype.val h
    ext u v
    have hp := congrArg
      (fun S : SimpleGraph (Sum (Sum (Fin n) Unit) Unit) =>
        S.Adj (e u) (e v)) heq
    simpa [f, SimpleGraph.comap_adj] using hp
  simpa [oldTrees, newTrees] using
    (Fintype.card_le_of_injective fSubtype hinj)

end YMUIC.Original24
