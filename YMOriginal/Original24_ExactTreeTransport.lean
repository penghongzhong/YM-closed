import YMOriginal.Original24_ExactGraphToSingleQ
import YMOriginal.Original24_PublishedPenroseExtended
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original 24: every exact two-root spanning tree transports to single-q

We DO NOT merely assert that the original two-root Mayer graph
has the same connectedness as a bulk-only polymer graph: q can
be a branching hub.  Instead, graph edges and trees are transported
through the strictly proven bijection

  Fin n ⊕ Fin 2 ≃ (Fin n ⊕ Unit) ⊕ Unit

with q retained as one polymer species. The augmented graph can
overcount a direct p-q contact. The only remaining FP combinatorial
task is the nonnegative labeled-tree weighted enumeration/recursion.
-/

/-- Every spanning tree of the TRUE hard-core n+2-vertex two-root
Mayer graph is a tree of the larger p-rooted, q-augmented graph
after the exact vertex equivalence, preserving ALL original edges.

In particular, q may be a hub of arbitrary degree. No combinatorial
Penrose/FP inequality or model-specific RG source bound is assumed.
This is the exact graph-to-tree bridge needed for the subsequent
positive finite-height q-fugacity coefficient extraction. -/
theorem original24_exact_spanning_tree_to_single_q
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ)
    (T : SimpleGraph (Sum (Fin n) (Fin 2)))
    (hT : T ∈ exactExtendedSpanningTrees n
      (actualExactTwoRootGraph n N chi rootP rootQ support tuple)) :
    ∃ T' : SimpleGraph (Sum (Sum (Fin n) Unit) Unit),
      T'.IsTree ∧
      T' ≤ actualSingleQRootGraph n N chi rootP rootQ support tuple ∧
      ∀ u v : Sum (Fin n) (Fin 2),
        T'.Adj (twoRootToSingleQ n u) (twoRootToSingleQ n v) ↔
          T.Adj u v := by
  classical
  have hmem :
      T ∈ (Finset.univ : Finset
        (SimpleGraph (Sum (Fin n) (Fin 2)))).filter
          (fun S => S ≤
            actualExactTwoRootGraph n N chi rootP rootQ support tuple ∧
            S.IsTree) := by
    simpa only [exactExtendedSpanningTrees] using hT
  obtain ⟨hSub, hTree⟩ := (Finset.mem_filter.mp hmem).2
  let e : Sum (Fin n) (Fin 2) ≃
      Sum (Sum (Fin n) Unit) Unit := twoRootToSingleQ n
  let T' : SimpleGraph (Sum (Sum (Fin n) Unit) Unit) :=
      SimpleGraph.comap e.symm T
  have hIso : T ≃g T' :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        simp [T', e] }
  have hTree' : T'.IsTree :=
    hIso.isTree_iff.mp hTree
  have hSub' :
      T' ≤ actualSingleQRootGraph n N chi rootP rootQ support tuple := by
    intro u v huv
    have hOrig : T.Adj (e.symm u) (e.symm v) := by
      simpa only [T', SimpleGraph.comap_adj] using huv
    have hOut :=
      original24_exact_graph_embeds_single_q
        n N chi rootP rootQ support tuple (e.symm u) (e.symm v)
        (hSub hOrig)
    simpa only [e, Equiv.apply_symm_apply] using hOut
  refine ⟨T', hTree', hSub', ?_⟩
  intro u v
  simp [T', e]

end YMUIC.Original24
