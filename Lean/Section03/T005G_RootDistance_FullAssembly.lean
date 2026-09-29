import Mathlib

set_option autoImplicit false

/-!
# U2 rooted support distance — full finite-graph assembly

This is the final standalone assembly corresponding to v133
`lem:root-distance`.

Extended vertices consist of n bulk polymers plus two external roots.
Every extended vertex carries a nonempty finite support in the physical block
graph.  Bulk supports have radius d(i); root supports have a uniform radius R.
Every allowed cluster edge has a physical contact witness at graph distance
at most chi.

For a connected rooted-cluster graph we extract a simple path between the two
roots, map it to physical support anchors, sum the edgewise metric budgets,
and use the fact that a simple path visits each extended vertex at most once.

The explicit constants are
  c_geo = chi + 2,
  c_rt  = chi + 4 R.
-/

namespace YMUICV128.Section03.T005G

abbrev RootLabel := Fin 2
def rootP : RootLabel := 0
def rootQ : RootLabel := 1
abbrev ExtendedVertex (n : ℕ) := Sum (Fin n) RootLabel

def vertexRadius {n : ℕ} (d : Fin n → ℕ) (R : ℕ) :
    ExtendedVertex n → ℕ
  | Sum.inl i => d i
  | Sum.inr _ => R

noncomputable def supportAnchor
    {V W : Type*}
    (S : W → Finset V)
    (hS : ∀ w : W, (S w).Nonempty)
    (w : W) : V :=
  Classical.choose (hS w)

theorem supportAnchor_mem
    {V W : Type*}
    (S : W → Finset V)
    (hS : ∀ w : W, (S w).Nonempty)
    (w : W) :
    supportAnchor S hS w ∈ S w :=
  Classical.choose_spec (hS w)

theorem anchor_edge_reachable
    {V W : Type*}
    (G : SimpleGraph V)
    (H : SimpleGraph W)
    (S : W → Finset V)
    (hS : ∀ w : W, (S w).Nonempty)
    (ρ : W → ℕ)
    (χ : ℕ)
    (hDiameter :
      ∀ (w : W) (a b : V),
        a ∈ S w → b ∈ S w →
        G.Reachable a b ∧ G.dist a b ≤ ρ w)
    (hContact :
      ∀ ⦃u v : W⦄, H.Adj u v →
        ∃ a : V, a ∈ S u ∧
        ∃ b : V, b ∈ S v ∧
          G.Reachable a b ∧ G.dist a b ≤ χ)
    {u v : W}
    (huv : H.Adj u v) :
    G.Reachable
      (supportAnchor S hS u)
      (supportAnchor S hS v) := by
  obtain ⟨a, ha, b, hb, habReach, _⟩ := hContact huv
  have hua :=
    hDiameter u (supportAnchor S hS u) a
      (supportAnchor_mem S hS u) ha
  have hbv :=
    hDiameter v b (supportAnchor S hS v)
      hb (supportAnchor_mem S hS v)
  exact hua.1.trans (habReach.trans hbv.1)

theorem anchor_edge_dist_le
    {V W : Type*}
    (G : SimpleGraph V)
    (H : SimpleGraph W)
    (S : W → Finset V)
    (hS : ∀ w : W, (S w).Nonempty)
    (ρ : W → ℕ)
    (χ : ℕ)
    (hDiameter :
      ∀ (w : W) (a b : V),
        a ∈ S w → b ∈ S w →
        G.Reachable a b ∧ G.dist a b ≤ ρ w)
    (hContact :
      ∀ ⦃u v : W⦄, H.Adj u v →
        ∃ a : V, a ∈ S u ∧
        ∃ b : V, b ∈ S v ∧
          G.Reachable a b ∧ G.dist a b ≤ χ)
    {u v : W}
    (huv : H.Adj u v) :
    G.dist
      (supportAnchor S hS u)
      (supportAnchor S hS v)
      ≤ ρ u + χ + ρ v := by
  obtain ⟨a, ha, b, hb, habReach, habDist⟩ := hContact huv
  have hua :=
    hDiameter u (supportAnchor S hS u) a
      (supportAnchor_mem S hS u) ha
  have hbv :=
    hDiameter v b (supportAnchor S hS v)
      hb (supportAnchor_mem S hS v)
  have h1 :
      G.dist (supportAnchor S hS u) (supportAnchor S hS v)
        ≤ G.dist (supportAnchor S hS u) a
          + G.dist a (supportAnchor S hS v) :=
    hua.1.dist_triangle_left (supportAnchor S hS v)
  have h2 :
      G.dist a (supportAnchor S hS v)
        ≤ G.dist a b + G.dist b (supportAnchor S hS v) :=
    habReach.dist_triangle_left (supportAnchor S hS v)
  omega

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

theorem edge_radius_cost_sum_le
    (ρ : ℕ → ℕ) (χ N : ℕ) :
    (Finset.range N).sum
        (fun k => ρ k + χ + ρ (k + 1))
      ≤
    2 * (Finset.range (N + 1)).sum ρ + χ * N := by
  have h₁ :
      (Finset.range N).sum ρ
        ≤ (Finset.range (N + 1)).sum ρ := by
    calc
      (Finset.range N).sum ρ
          ≤ (Finset.range N).sum ρ + ρ N :=
            Nat.le_add_right _ _
      _ = (Finset.range (N + 1)).sum ρ := by
            rw [Finset.sum_range_succ]
  have h₂ :
      (Finset.range N).sum (fun k => ρ (k + 1))
        ≤ (Finset.range (N + 1)).sum ρ := by
    rw [Finset.sum_range_succ']
    omega
  have hsplit :
      (Finset.range N).sum
          (fun k => ρ k + χ + ρ (k + 1))
        =
      (Finset.range N).sum ρ
        + χ * N
        + (Finset.range N).sum (fun k => ρ (k + 1)) := by
    simp [Finset.sum_add_distrib, Nat.mul_comm, add_assoc]
  rw [hsplit]
  omega

theorem extendedVertex_card (n : ℕ) :
    Fintype.card (ExtendedVertex n) = n + 2 := by
  simp [ExtendedVertex, RootLabel]

theorem bulk_count_le_total_length
    {n : ℕ}
    (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, 1 ≤ d i) :
    n ≤ ∑ i : Fin n, d i := by
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, d i := by
      exact Finset.sum_le_sum fun i _ => hd i

theorem simple_root_path_length_le_total
    {n : ℕ}
    {H : SimpleGraph (ExtendedVertex n)}
    {u v : ExtendedVertex n}
    (p : H.Walk u v)
    (hp : p.IsPath)
    (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, 1 ≤ d i) :
    p.length ≤ (∑ i : Fin n, d i) + 1 := by
  have hlt : p.length < Fintype.card (ExtendedVertex n) :=
    hp.length_lt
  rw [extendedVertex_card] at hlt
  have hbulk := bulk_count_le_total_length d hd
  omega

theorem getVert_range_sum_eq_support_sum
    {V : Type*}
    {G : SimpleGraph V}
    (f : V → ℕ)
    {u v : V}
    (p : G.Walk u v) :
    (Finset.range (p.length + 1)).sum
        (fun k => f (p.getVert k))
      = (p.support.map f).sum := by
  induction p with
  | nil =>
      simp
  | @cons u v w h p ih =>
      calc
        (Finset.range ((p.cons h).length + 1)).sum
            (fun k => f ((p.cons h).getVert k))
            =
          f u + (Finset.range (p.length + 1)).sum
            (fun k => f (p.getVert k)) := by
              rw [show (p.cons h).length + 1 = (p.length + 1) + 1 by simp]
              rw [Finset.sum_range_succ']
              simp [Nat.add_comm]
        _ = f u + (p.support.map f).sum := by
              rw [ih]
        _ = ((p.cons h).support.map f).sum := by
              simp

theorem total_vertexRadius
    {n : ℕ}
    (d : Fin n → ℕ)
    (R : ℕ) :
    (∑ v : ExtendedVertex n, vertexRadius d R v)
      = (∑ i : Fin n, d i) + 2 * R := by
  rw [Fintype.sum_sum_type]
  simp [vertexRadius, two_mul]

theorem simple_path_getVert_radius_sum_le_total
    {n : ℕ}
    {H : SimpleGraph (ExtendedVertex n)}
    {u v : ExtendedVertex n}
    (p : H.Walk u v)
    (hp : p.IsPath)
    (d : Fin n → ℕ)
    (R : ℕ) :
    (Finset.range (p.length + 1)).sum
        (fun k => vertexRadius d R (p.getVert k))
      ≤ (∑ i : Fin n, d i) + 2 * R := by
  classical
  rw [getVert_range_sum_eq_support_sum]
  calc
    (p.support.map (vertexRadius d R)).sum
        = ∑ x ∈ p.support.toFinset, vertexRadius d R x := by
            symm
            exact List.sum_toFinset _ hp.support_nodup
    _ ≤ ∑ x ∈ (Finset.univ : Finset (ExtendedVertex n)),
          vertexRadius d R x :=
      Finset.sum_le_sum_of_subset (by
        intro x hx
        simp)
    _ = ∑ x : ExtendedVertex n, vertexRadius d R x := by
      rfl
    _ = (∑ i : Fin n, d i) + 2 * R :=
      total_vertexRadius d R

theorem rooted_anchor_distance_explicit
    {V : Type*}
    {n : ℕ}
    (G : SimpleGraph V)
    (H : SimpleGraph (ExtendedVertex n))
    (S : ExtendedVertex n → Finset V)
    (hS : ∀ w : ExtendedVertex n, (S w).Nonempty)
    (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, 1 ≤ d i)
    (R χ : ℕ)
    (hDiameter :
      ∀ (w : ExtendedVertex n) (a b : V),
        a ∈ S w → b ∈ S w →
        G.Reachable a b ∧
          G.dist a b ≤ vertexRadius d R w)
    (hContact :
      ∀ ⦃u v : ExtendedVertex n⦄, H.Adj u v →
        ∃ a : V, a ∈ S u ∧
        ∃ b : V, b ∈ S v ∧
          G.Reachable a b ∧ G.dist a b ≤ χ)
    (hconn : H.Connected) :
    G.dist
      (supportAnchor S hS (Sum.inr rootP))
      (supportAnchor S hS (Sum.inr rootQ))
      ≤
    (χ + 2) * (∑ i : Fin n, d i) + (χ + 4 * R) := by
  obtain ⟨p, hp⟩ :=
    hconn.exists_isPath
      (Sum.inr rootP : ExtendedVertex n)
      (Sum.inr rootQ : ExtendedVertex n)
  let anchor : ExtendedVertex n → V := supportAnchor S hS
  let edgeCost : ExtendedVertex n → ExtendedVertex n → ℕ :=
    fun u v => vertexRadius d R u + χ + vertexRadius d R v
  have hEdgeReach :
      ∀ ⦃u v : ExtendedVertex n⦄, H.Adj u v →
        G.Reachable (anchor u) (anchor v) := by
    intro u v huv
    exact anchor_edge_reachable
      G H S hS (vertexRadius d R) χ hDiameter hContact huv
  have hEdgeCost :
      ∀ ⦃u v : ExtendedVertex n⦄, H.Adj u v →
        G.dist (anchor u) (anchor v) ≤ edgeCost u v := by
    intro u v huv
    exact anchor_edge_dist_le
      G H S hS (vertexRadius d R) χ hDiameter hContact huv
  have hmap :
      G.dist
        (anchor (Sum.inr rootP))
        (anchor (Sum.inr rootQ))
        ≤
      (Finset.range p.length).sum
        (fun k =>
          edgeCost (p.getVert k) (p.getVert (k + 1))) :=
    mapped_walk_dist_le_sum
      G H anchor edgeCost hEdgeReach hEdgeCost p
  have hedge :
      (Finset.range p.length).sum
        (fun k =>
          vertexRadius d R (p.getVert k) + χ
            + vertexRadius d R (p.getVert (k + 1)))
        ≤
      2 * (Finset.range (p.length + 1)).sum
          (fun k => vertexRadius d R (p.getVert k))
        + χ * p.length :=
    edge_radius_cost_sum_le
      (fun k => vertexRadius d R (p.getVert k)) χ p.length
  have hradius :
      (Finset.range (p.length + 1)).sum
          (fun k => vertexRadius d R (p.getVert k))
        ≤ (∑ i : Fin n, d i) + 2 * R :=
    simple_path_getVert_radius_sum_le_total p hp d R
  have hlen :
      p.length ≤ (∑ i : Fin n, d i) + 1 :=
    simple_root_path_length_le_total p hp d hd
  have hrad2 :
      2 * (Finset.range (p.length + 1)).sum
          (fun k => vertexRadius d R (p.getVert k))
        ≤
      2 * ((∑ i : Fin n, d i) + 2 * R) :=
    Nat.mul_le_mul_left 2 hradius
  have hlenχ :
      χ * p.length ≤ χ * ((∑ i : Fin n, d i) + 1) :=
    Nat.mul_le_mul_left χ hlen
  calc
    G.dist
        (supportAnchor S hS (Sum.inr rootP))
        (supportAnchor S hS (Sum.inr rootQ))
        =
      G.dist
        (anchor (Sum.inr rootP))
        (anchor (Sum.inr rootQ)) := by
          rfl
    _ ≤
      (Finset.range p.length).sum
        (fun k =>
          edgeCost (p.getVert k) (p.getVert (k + 1))) :=
      hmap
    _ =
      (Finset.range p.length).sum
        (fun k =>
          vertexRadius d R (p.getVert k) + χ
            + vertexRadius d R (p.getVert (k + 1))) := by
      rfl
    _ ≤
      2 * (Finset.range (p.length + 1)).sum
          (fun k => vertexRadius d R (p.getVert k))
        + χ * p.length :=
      hedge
    _ ≤
      2 * ((∑ i : Fin n, d i) + 2 * R)
        + χ * p.length :=
      Nat.add_le_add hrad2 (le_refl _)
    _ ≤
      2 * ((∑ i : Fin n, d i) + 2 * R)
        + χ * ((∑ i : Fin n, d i) + 1) :=
      Nat.add_le_add_left hlenχ _
    _ =
      (χ + 2) * (∑ i : Fin n, d i)
        + (χ + 4 * R) := by
      ring

theorem rooted_support_distance_constants_exist
    {V : Type*}
    {n : ℕ}
    (G : SimpleGraph V)
    (H : SimpleGraph (ExtendedVertex n))
    (S : ExtendedVertex n → Finset V)
    (hS : ∀ w : ExtendedVertex n, (S w).Nonempty)
    (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, 1 ≤ d i)
    (R χ : ℕ)
    (hDiameter :
      ∀ (w : ExtendedVertex n) (a b : V),
        a ∈ S w → b ∈ S w →
        G.Reachable a b ∧
          G.dist a b ≤ vertexRadius d R w)
    (hContact :
      ∀ ⦃u v : ExtendedVertex n⦄, H.Adj u v →
        ∃ a : V, a ∈ S u ∧
        ∃ b : V, b ∈ S v ∧
          G.Reachable a b ∧ G.dist a b ≤ χ)
    (hconn : H.Connected) :
    ∃ cGeo cRt : ℕ,
      1 ≤ cGeo ∧
      G.dist
        (supportAnchor S hS (Sum.inr rootP))
        (supportAnchor S hS (Sum.inr rootQ))
        ≤ cGeo * (∑ i : Fin n, d i) + cRt := by
  refine ⟨χ + 2, χ + 4 * R, by omega, ?_⟩
  exact rooted_anchor_distance_explicit
    G H S hS d hd R χ hDiameter hContact hconn

#print axioms rooted_anchor_distance_explicit
#print axioms rooted_support_distance_constants_exist

end YMUICV128.Section03.T005G
