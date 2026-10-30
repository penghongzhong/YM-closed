import YMOriginal.Original24_LocalGaugeInvariance

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Genuine link-based lattice SU(2) Wilson loop source dictionary

The earlier source grammar treated finite plaquette/word holonomies
as SU(2) inputs. Here the ordered words are constructed FROM ACTUAL
lattice link transport U : Vertex -> Vertex -> SU2.

For arbitrary independent site gauges g : Vertex -> SU2,
  U^g(x,y) = g(x) U(x,y) g(y)^(-1).
The gauge factors telescope along every actual oriented walk, leaving
only the endpoint gauge factors. Every closed based Wilson loop is
thus gauge-invariant under the *full sitewise gauge group*, not just
an imposed common-basepoint SU2 conjugation. The same holds for
arbitrary fixed finite products and linear combinations of closed
Wilson loops. The root normalization and jet map are still separate
physical RG tasks.
-/

/-- An oriented finite link path from `base` through each listed vertex. -/
def actualWalkHolonomy {Vertex : Type*}
    (U : Vertex → Vertex → SU2) (base : Vertex) :
    List Vertex → SU2
  | [] => 1
  | v :: rest => U base v * actualWalkHolonomy U v rest

/-- Last vertex of the ordered walk, with empty walk ending at base. -/
def actualWalkEndpoint {Vertex : Type*} (base : Vertex) :
    List Vertex → Vertex
  | [] => base
  | v :: rest => actualWalkEndpoint v rest

/-- True sitewise lattice link gauge transform. -/
def transformedLink {Vertex : Type*}
    (g : Vertex → SU2) (U : Vertex → Vertex → SU2) :
    Vertex → Vertex → SU2 :=
  fun x y => g x * U x y * (g y)⁻¹

/-- Exact open-path covariance, proven by cancellation of every
interior site's independent SU2 gauge factor. -/
theorem actual_walk_gauge_transport
    {Vertex : Type*}
    (g : Vertex → SU2) (U : Vertex → Vertex → SU2)
    (base : Vertex) (vertices : List Vertex) :
    actualWalkHolonomy (transformedLink g U) base vertices *
      g (actualWalkEndpoint base vertices) =
    g base * actualWalkHolonomy U base vertices := by
  induction vertices generalizing base with
  | nil =>
      simp [actualWalkHolonomy, actualWalkEndpoint]
  | cons v rest ih =>
      change
        ((g base * U base v * (g v)⁻¹) *
          actualWalkHolonomy (transformedLink g U) v rest) *
          g (actualWalkEndpoint v rest) =
        g base * (U base v * actualWalkHolonomy U v rest)
      calc
        _ = (g base * U base v * (g v)⁻¹) *
          (actualWalkHolonomy (transformedLink g U) v rest *
            g (actualWalkEndpoint v rest)) := by group
        _ = (g base * U base v * (g v)⁻¹) *
          (g v * actualWalkHolonomy U v rest) := by rw [ih v]
        _ = _ := by group

/-- A genuine finite closed oriented lattice loop at a fixed site. -/
structure ClosedLinkWalkAt (Vertex : Type*) (base : Vertex) where
  vertices : List Vertex
  closes : actualWalkEndpoint base vertices = base

/-- Every actual closed based lattice loop transforms by only its
basepoint conjugation, with all intermediate site transformations gone. -/
theorem actual_closed_link_walk_conjugacy
    {Vertex : Type*} (g : Vertex → SU2)
    (U : Vertex → Vertex → SU2)
    (base : Vertex) (w : ClosedLinkWalkAt Vertex base) :
    actualWalkHolonomy (transformedLink g U) base w.vertices =
      g base * actualWalkHolonomy U base w.vertices * (g base)⁻¹ := by
  have h := actual_walk_gauge_transport g U base w.vertices
  rw [w.closes] at h
  calc
    actualWalkHolonomy (transformedLink g U) base w.vertices =
      (actualWalkHolonomy (transformedLink g U) base w.vertices *
        g base) * (g base)⁻¹ := by group
    _ = (g base * actualWalkHolonomy U base w.vertices) *
        (g base)⁻¹ := by rw [h]
    _ = _ := by group

/-- True loop-root (trace, not a synthetic source variable). -/
def actualClosedWilsonRoot {Vertex : Type*} (base : Vertex)
    (U : Vertex → Vertex → SU2) (w : ClosedLinkWalkAt Vertex base) : ℝ :=
  wilsonRoot (actualWalkHolonomy U base w.vertices)

/-- Local SU2 gauge invariance for every link-based Wilson loop root. -/
theorem actual_closed_wilson_root_gauge_invariant
    {Vertex : Type*} (base : Vertex)
    (g : Vertex → SU2) (U : Vertex → Vertex → SU2)
    (w : ClosedLinkWalkAt Vertex base) :
    actualClosedWilsonRoot base (transformedLink g U) w =
      actualClosedWilsonRoot base U w := by
  unfold actualClosedWilsonRoot
  rw [actual_closed_link_walk_conjugacy]
  exact wilson_root_conjugation_invariant _ _

/-- The original fixed-D gauge-invariant source grammar, now made of
actual ordered lattice links and closed loops, with finite word
products and coefficients (no bound on total gauge sites needed). -/
def actualLinkWilsonPolynomial
    {Vertex T : Type*} [Fintype T]
    (base : Vertex) (U : Vertex → Vertex → SU2)
    (words : T → List (List (ClosedLinkWalkAt Vertex base)))
    (coeff : T → ℂ) : ℂ :=
  actualWilsonPolynomial
    (fun w : ClosedLinkWalkAt Vertex base =>
      actualWalkHolonomy U base w.vertices)
    words coeff

/-- Any actual finite polynomial of closed Wilson words is gauge
invariant under an arbitrary independent site gauge at EVERY vertex. -/
theorem actual_link_wilson_polynomial_gauge_invariant
    {Vertex T : Type*} [Fintype T]
    (base : Vertex) (g : Vertex → SU2)
    (U : Vertex → Vertex → SU2)
    (words : T → List (List (ClosedLinkWalkAt Vertex base)))
    (coeff : T → ℂ) :
    actualLinkWilsonPolynomial base (transformedLink g U) words coeff =
      actualLinkWilsonPolynomial base U words coeff := by
  have hpoint :
      (fun w : ClosedLinkWalkAt Vertex base =>
        actualWalkHolonomy (transformedLink g U) base w.vertices) =
      (fun w : ClosedLinkWalkAt Vertex base =>
        g base * actualWalkHolonomy U base w.vertices * (g base)⁻¹) := by
    funext w
    exact actual_closed_link_walk_conjugacy g U base w
  unfold actualLinkWilsonPolynomial
  rw [hpoint]
  exact actual_wilson_polynomial_gauge_invariant (g base)
    (fun w : ClosedLinkWalkAt Vertex base =>
      actualWalkHolonomy U base w.vertices)
    words coeff

end YMUIC.Original24
