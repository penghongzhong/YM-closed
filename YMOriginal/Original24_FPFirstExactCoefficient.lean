import YMOriginal.Original24_FPFirstGraph
import YMOriginal.Original24_FPFirstConnectedBulk
import YMOriginal.Original24_ExactExtendedWeighted
import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original24: COMPLETE n=1 exact Mayer tree coefficient → positive KP

We audit the literal 3-vertex (p, bulk, q) n=1 Mayer graph, with NO
direct p-q edge.  If connected, it is itself the UNIQUE spanning tree;
if not connected, no spanning tree exists. This is deduced from the
actual no-root-root Mayer relation, and uses no Penrose or FP input.

Therefore its exact physical 1/1! positive tree coefficient agrees
with the sum of activity norms of bulk polymers touching both roots.
Combining with the previously strict KP recursion closes the EXACT
n=1 instance of the two-root positive FP comparison (at h+1).

The all-n original PhysicalExactTwoRootFPCriterion remains OPEN.
-/

/-- The maximal possible n=1 two-root graph is the three-vertex
star (p -- bulk -- q). It is a literal tree, with no p-q bond. -/
private def oneBulkStar : SimpleGraph (Sum (Fin 1) (Fin 2)) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False)

private theorem oneBulkStar_isTree : oneBulkStar.IsTree := by
  decide

private theorem actual_one_bulk_graph_le_star
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 1 → Γ) :
    actualExactTwoRootGraph 1 N chi rootP rootQ support tuple
      ≤ oneBulkStar := by
  intro u v h
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          fin_cases i
          fin_cases j
          exact ((SimpleGraph.ne_of_adj h) rfl).elim
      | inr k =>
          simp [oneBulkStar, SimpleGraph.fromRel_adj]
  | inr i =>
      cases v with
      | inl j =>
          simp [oneBulkStar, SimpleGraph.fromRel_adj]
      | inr k =>
          have hn :
              ¬ (actualExactTwoRootGraph 1 N chi rootP rootQ
                support tuple).Adj (Sum.inr i) (Sum.inr k) := by
            simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
              SimpleGraph.fromRel_adj]
          exact (hn h).elim

/-- Nonzero n=1 connected Mayer geometry is a tree itself, with no
unproven counting or published tree inequality. -/
theorem original24_one_bulk_connected_isTree
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 1 → Γ)
    (hc : (actualExactTwoRootGraph 1 N chi
      rootP rootQ support tuple).Connected) :
    (actualExactTwoRootGraph 1 N chi
      rootP rootQ support tuple).IsTree :=
  ⟨hc, oneBulkStar_isTree.isAcyclic.anti
    (actual_one_bulk_graph_le_star N chi rootP rootQ support tuple)⟩

/-- Exact spanning tree count, for all true 4D regulator data,
all source supports and all polymer species: either one path, or zero. -/
theorem original24_one_bulk_exact_tree_count
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin 1 → Γ) :
    (exactExtendedSpanningTrees 1
      (actualExactTwoRootGraph 1 N chi
        rootP rootQ support tuple)).card =
    if (actualExactTwoRootGraph 1 N chi
      rootP rootQ support tuple).Connected then 1 else 0 := by
  classical
  let G := actualExactTwoRootGraph 1 N chi
    rootP rootQ support tuple
  by_cases hc : G.Connected
  · have hG : G.IsTree :=
      original24_one_bulk_connected_isTree
        N chi rootP rootQ support tuple hc
    have hMin : Minimal (fun T : SimpleGraph (Sum (Fin 1) (Fin 2)) =>
        T.Connected) G :=
      SimpleGraph.isTree_iff_minimal_connected.mp hG
    have hset : exactExtendedSpanningTrees 1 G = {G} := by
      ext T
      simp only [exactExtendedSpanningTrees, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ht
        exact le_antisymm ht.1
          (hMin.le_of_le ht.2.connected ht.1)
      · intro heq
        subst T
        exact ⟨le_refl _, hG⟩
    simp [hc, hset]
  · have hset : exactExtendedSpanningTrees 1 G = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro T hT
      have hsub : T ≤ G ∧ T.IsTree := by
        simpa only [exactExtendedSpanningTrees,
          Finset.mem_filter, Finset.mem_univ, true_and] using hT
      exact hc (hsub.2.connected.mono hsub.1)
    simp [hc, hset]

/-- The EXACT first nonzero n=1 2-root spanning-tree coefficient,
with no hFP/graph-tree hypothesis, is literally the total activity
of actual 4D polymers touching both physical Wilson roots. -/
theorem original24_exact_first_tree_majorant_eq_bridge
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    exactExtendedTwoRootTreeMajorant 1 N chi
      rootP rootQ support z =
    ∑ X ∈ actualOnePolymerTwoRootBridge N chi
      rootP rootQ support, ‖z X‖ := by
  classical
  let A := actualOnePolymerTwoRootBridge N chi
    rootP rootQ support
  have hsum :
      (∑ tuple : Fin 1 → Γ,
        if (actualExactTwoRootGraph 1 N chi
            rootP rootQ support tuple).Connected then
          ((exactExtendedSpanningTrees 1
             (actualExactTwoRootGraph 1 N chi
               rootP rootQ support tuple)).card : ℝ) *
            ∏ i : Fin 1, ‖z (tuple i)‖
        else 0) =
      ∑ X : Γ, if X ∈ A then ‖z X‖ else 0 := by
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) Γ)
    intro tuple
    have hConn :=
      original24_exact_one_bulk_graph_connected_iff
        N chi rootP rootQ support tuple
    have hTree :=
      original24_one_bulk_exact_tree_count
        N chi rootP rootQ support tuple
    by_cases h : (actualExactTwoRootGraph 1 N chi
      rootP rootQ support tuple).Connected
    · have hX : tuple 0 ∈ A := hConn.mp h
      simp [h, hX, hTree, A, Equiv.funUnique]
    · have hX : tuple 0 ∉ A := fun hx => h (hConn.mpr hx)
      simp [h, hX, A, Equiv.funUnique]
  unfold exactExtendedTwoRootTreeMajorant
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
  rw [hsum]
  simp [A, Finset.sum_filter]

/-- The desired physical FP inequality is STRICTLY PROVED at its
first nonzero order, not assumed. It uses the exact graph coefficient
(including n+2 graph and 1/n!) and true one-q KP recursion, with the
physically correct sign cGeo*mu≥0. The h+1 height is explicit. -/
theorem original24_exact_first_FP_coefficient_from_U1
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu lam eps : ℝ)
    (hgeom : 0 ≤ cGeo * mu)
    (hlam : 1 ≤ lam) (heps : 0 < eps)
    (h : ℕ) :
    lam * eps *
      exactExtendedTwoRootTreeMajorant 1 N chi
        rootP rootQ support z ≤
    Real.exp
      (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity
          (fun X => (lam : ℂ) * z X) eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu (h + 1)) - 1 := by
  have hKP := original24_FP_one_bulk_connected_from_KP
    N chi rootP rootQ support z d cGeo mu lam eps
    hgeom hlam heps h
  rw [original24_exact_first_tree_majorant_eq_bridge]
  calc
    lam * eps *
        (∑ X ∈ actualOnePolymerTwoRootBridge N chi
          rootP rootQ support, ‖z X‖) =
      ∑ X ∈ actualOnePolymerTwoRootBridge N chi
        rootP rootQ support, lam * eps * ‖z X‖ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          ring
    _ ≤ _ := hKP

end YMUIC.Original24
