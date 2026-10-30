import YMOriginal.Original24_ActualLatticeLinks
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Actual bounded-complexity lattice Wilson-root support geometry

The C29 source roots are actual finite NN (nearest-neighbor) closed
SU2 link paths, not arbitrary SU2 symbols. From a genuine lattice
site metric where each NN link has length <= a, the support of a
word with <= L links stays within physical radius L*a of its base.

For two roots p,q, every pair of support points is at distance
<= dist(p,q) + 2*L*a. The support constant L depends ONLY on the
fixed word template, not on a, j, UV cutoff or lattice volume.
This checks the root-support-radius input to the already Lean-verified
v133 rooted distance geometry, but does not prove the CMP119/122
polymer-history contact dictionary.
-/

/-- Genuine path-local nearest-neighbor validity, verified at every
consecutive oriented edge of the actual site sequence. -/
def ValidNearestWalk {Vertex : Type*}
    (NN : Vertex → Vertex → Prop) (base : Vertex) :
    List Vertex → Prop
  | [] => True
  | v :: rest => NN base v ∧ ValidNearestWalk NN v rest

/-- Every site visited by a true nearest-neighbor path is within
its number of edges times a of the basepoint. -/
theorem actual_link_walk_support_radius
    {Vertex Space : Type*} [PseudoMetricSpace Space]
    (position : Vertex → Space)
    (NN : Vertex → Vertex → Prop)
    (a : ℝ) (ha : 0 ≤ a)
    (hNN : ∀ u v, NN u v →
      dist (position u) (position v) ≤ a)
    (base : Vertex) (walk : List Vertex)
    (hValid : ValidNearestWalk NN base walk) :
    ∀ v ∈ walk,
      dist (position base) (position v) ≤
        (walk.length : ℝ) * a := by
  induction walk generalizing base with
  | nil =>
      intro v hv
      simp at hv
  | cons nxt rest ih =>
      change NN base nxt ∧ ValidNearestWalk NN nxt rest at hValid
      obtain ⟨hEdge, hRest⟩ := hValid
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · calc
          dist (position base) (position v) ≤ a :=
            hNN base v hEdge
          _ ≤ ((v :: rest).length : ℝ) * a := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            have hlen : (0 : ℝ) ≤ rest.length :=
              Nat.cast_nonneg _
            nlinarith
      · calc
          dist (position base) (position v) ≤
            dist (position base) (position nxt) +
              dist (position nxt) (position v) :=
                dist_triangle _ _ _
          _ ≤ a + (rest.length : ℝ) * a :=
            add_le_add (hNN base nxt hEdge) (ih nxt hRest v hv)
          _ = ((nxt :: rest).length : ℝ) * a := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring

/-- Bounded fixed-template word length yields a cutoff/volume
independent physical support-radius constant L. -/
theorem actual_fixed_word_support_radius
    {Vertex Space : Type*} [PseudoMetricSpace Space]
    (position : Vertex → Space)
    (NN : Vertex → Vertex → Prop)
    (a : ℝ) (ha : 0 ≤ a)
    (hNN : ∀ u v, NN u v →
      dist (position u) (position v) ≤ a)
    (L : ℕ) (base : Vertex) (walk : List Vertex)
    (hLength : walk.length ≤ L)
    (hValid : ValidNearestWalk NN base walk) :
    ∀ v ∈ walk, dist (position base) (position v) ≤ (L : ℝ) * a := by
  intro v hv
  exact (actual_link_walk_support_radius position NN
    a ha hNN base walk hValid v hv).trans
      (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hLength) ha)

/-- Support separation for two TRUE finite link words at possibly
distinct lattice basepoints, with a uniform 2*L*a root overhead. -/
theorem actual_two_fixed_wilson_root_support_separation
    {Vertex Space : Type*} [PseudoMetricSpace Space]
    (position : Vertex → Space)
    (NN : Vertex → Vertex → Prop)
    (a : ℝ) (ha : 0 ≤ a)
    (hNN : ∀ u v, NN u v →
      dist (position u) (position v) ≤ a)
    (L : ℕ) (baseP baseQ : Vertex)
    (wp wq : List Vertex)
    (hLengthP : wp.length ≤ L) (hLengthQ : wq.length ≤ L)
    (hValidP : ValidNearestWalk NN baseP wp)
    (hValidQ : ValidNearestWalk NN baseQ wq)
    (p q : Vertex) (hp : p ∈ wp) (hq : q ∈ wq) :
    dist (position p) (position q) ≤
      dist (position baseP) (position baseQ) + 2 * (L : ℝ) * a := by
  have hrp := actual_fixed_word_support_radius
    position NN a ha hNN L baseP wp hLengthP hValidP p hp
  have hrq := actual_fixed_word_support_radius
    position NN a ha hNN L baseQ wq hLengthQ hValidQ q hq
  calc
    dist (position p) (position q) ≤
      dist (position p) (position baseP) +
        dist (position baseP) (position q) :=
        dist_triangle _ _ _
    _ ≤ dist (position p) (position baseP) +
      (dist (position baseP) (position baseQ) +
        dist (position baseQ) (position q)) := by
          have htri := dist_triangle
            (position baseP) (position baseQ) (position q)
          linarith
    _ ≤ (L : ℝ) * a +
      (dist (position baseP) (position baseQ) + (L : ℝ) * a) := by
          have hpr :
              dist (position p) (position baseP) ≤ (L : ℝ) * a := by
            rw [dist_comm]
            exact hrp
          linarith
    _ = dist (position baseP) (position baseQ) +
      2 * (L : ℝ) * a := by ring

end YMUIC.Original24
