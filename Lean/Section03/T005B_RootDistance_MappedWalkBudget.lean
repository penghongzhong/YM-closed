import Mathlib

set_option autoImplicit false

/-!
# U2 root-distance: generic mapped-walk metric budget

Standalone triangle-budget certificate used by v133 `lem:root-distance`.

For a finite walk in an auxiliary/rooted-cluster graph, if every auxiliary
edge maps to a reachable pair in the physical block graph with a prescribed
distance cost, then the physical endpoint distance is bounded by the sum of
those edge costs.

No Yang--Mills contact estimate is assumed implicitly; edgewise reachability
and edgewise distance bounds are explicit hypotheses.
-/

namespace YMUICV128.Section03.T005B

theorem dist_chain_le_sum
    {V : Type*}
    (G : SimpleGraph V)
    (x : ℕ → V)
    (cost : ℕ → ℕ)
    (N : ℕ)
    (hReach :
      ∀ k : ℕ, k < N →
        G.Reachable (x k) (x (k + 1)))
    (hCost :
      ∀ k : ℕ, k < N →
        G.dist (x k) (x (k + 1)) ≤ cost k) :
    G.dist (x 0) (x N) ≤ (Finset.range N).sum cost := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hReachPrev :
          ∀ k : ℕ, k < N →
            G.Reachable (x k) (x (k + 1)) := by
        intro k hk
        exact hReach k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have hCostPrev :
          ∀ k : ℕ, k < N →
            G.dist (x k) (x (k + 1)) ≤ cost k := by
        intro k hk
        exact hCost k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have hIH :
          G.dist (x 0) (x N) ≤ (Finset.range N).sum cost :=
        ih hReachPrev hCostPrev
      have hLastReach :
          G.Reachable (x N) (x (N + 1)) :=
        hReach N (Nat.lt_succ_self N)
      have hLastCost :
          G.dist (x N) (x (N + 1)) ≤ cost N :=
        hCost N (Nat.lt_succ_self N)
      calc
        G.dist (x 0) (x (Nat.succ N))
            ≤ G.dist (x 0) (x N) + G.dist (x N) (x (N + 1)) := by
                simpa [Nat.succ_eq_add_one] using
                  hLastReach.dist_triangle_right (x 0)
        _ ≤ (Finset.range N).sum cost + cost N :=
              Nat.add_le_add hIH hLastCost
        _ = (Finset.range (Nat.succ N)).sum cost := by
              simp [Finset.sum_range_succ]

theorem mapped_walk_dist_le_sum
    {V W : Type*}
    (G : SimpleGraph V)
    (H : SimpleGraph W)
    (anchor : W → V)
    (edgeCost : W → W → ℕ)
    (hEdgeReach :
      ∀ ⦃u v : W⦄, H.Adj u v →
        G.Reachable (anchor u) (anchor v))
    (hEdgeCost :
      ∀ ⦃u v : W⦄, H.Adj u v →
        G.dist (anchor u) (anchor v) ≤ edgeCost u v)
    {u v : W}
    (p : H.Walk u v) :
    G.dist (anchor u) (anchor v) ≤
      (Finset.range p.length).sum
        (fun k => edgeCost (p.getVert k) (p.getVert (k + 1))) := by
  let x : ℕ → V := fun k => anchor (p.getVert k)
  let c : ℕ → ℕ :=
    fun k => edgeCost (p.getVert k) (p.getVert (k + 1))
  have h :
      G.dist (x 0) (x p.length) ≤
        (Finset.range p.length).sum c := by
    apply dist_chain_le_sum G x c p.length
    · intro k hk
      exact hEdgeReach (p.adj_getVert_succ hk)
    · intro k hk
      exact hEdgeCost (p.adj_getVert_succ hk)
  simpa [x, c] using h

#print axioms dist_chain_le_sum
#print axioms mapped_walk_dist_le_sum

end YMUICV128.Section03.T005B
