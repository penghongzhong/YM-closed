import Mathlib

set_option autoImplicit false

/-!
# U2 root-distance: support anchors and one-edge physical budget

Standalone geometric certificate.

Let each auxiliary/rooted-cluster vertex u carry a nonempty finite physical
support S(u) in the block graph.  Assume:
* every two points of S(u) are physically reachable and have distance ≤ ρ(u);
* every auxiliary edge u~v has contact witnesses a∈S(u), b∈S(v) with
  physical distance ≤ χ.

Choosing one canonical anchor in every support gives, for every auxiliary edge,

  dist(anchor u, anchor v) ≤ ρ(u) + χ + ρ(v).

This is exactly the local edge estimate needed before summing along the
root-to-root cluster path.  No global root-distance conclusion is claimed here.
-/

namespace YMUICV128.Section03.T005C

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

#print axioms supportAnchor_mem
#print axioms anchor_edge_reachable
#print axioms anchor_edge_dist_le

end YMUICV128.Section03.T005C
