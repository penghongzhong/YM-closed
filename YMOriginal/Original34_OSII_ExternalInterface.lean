import YM.OSTensor.JointSchwartzControl
import Mathlib

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original34

/-!
# Original #34: Osterwalder--Schrader 1975 Theorem E' -> R'

The 2026-10-30 strengthened source enforces S_0=1 and the FULL E1
Euclidean action (translations and rotations) as model-side hypotheses;
the earlier type missed these physical normalization/covariance inputs.
# EXACT PUBLISHED-INPUT USE BOUNDARY (not a new proof of OS II).

Osterwalder--Schrader, "Axioms for Euclidean Green's Functions II",
Commun. Math. Phys. 42 (1975), 281--305, Section IV.1--IV.2
(pp. 287--288): corrected E0' plus E1--E4 implies
reconstruction of the Wightman hierarchy.

The actual model's full joint-test E0' and E1--E4 remain obligations
of Original30/25/28/32/33; NO replacement by pure tensor moments or
a hypothesized target Wightman hierarchy is accepted.

This is a published-external-implication interface check like
Original01 (Balaban U1). It is NOT an internal construction of
the OS Hilbert space or analytic continuation, and cannot be
misreported as proving the missing Original30 physical growth.
-/

/-- The genuine joint 4r-variable Schwartz test space. -/
abbrev JointTest (r : ℕ) :=
  SchwartzMap (EuclideanSpace ℝ (Fin (4 * r))) ℂ

/-- Joint continuous Euclidean Schwinger distributions, not merely a
family of multilinear forms on products of one-variable tests. -/
structure SchwingerHierarchy where
  S : (r : ℕ) → JointTest r →L[ℂ] ℂ

/-- The geometric operations used to state the E1--E4 assumptions.
All four are fixed once, and not allowed to depend on the cutoff.
The physical source-to-test geometry dictionary must still be checked. -/
structure OSTestGeometry (Rot PosPoly : Type*) where
  rotate : ∀ r, Rot → JointTest r → JointTest r
  translate : ∀ r, EuclideanSpace ℝ (Fin 4) → JointTest r → JointTest r
  permute : ∀ r, Equiv.Perm (Fin r) → JointTest r → JointTest r
  separate : ∀ r s, JointTest r → JointTest s → ℝ → JointTest (r + s)
  positiveTime : PosPoly → Prop
  reflectedPolynomialMoment : SchwingerHierarchy → PosPoly → PosPoly → ℂ

/-- Corrected, factorial, LINEAR-DERIVATIVE-ORDER joint-test E0'.
This demands a bound on true joint Schwartz tests; the naive
pure-tensor estimate is deliberately insufficient. -/
def OS_E0prime (H : SchwingerHierarchy) : Prop :=
  ∃ (q k : ℕ) (A C : ℝ), 0 ≤ A ∧ 0 < C ∧
    ∀ (r : ℕ) (f : JointTest r),
      ‖H.S r f‖ ≤
        (A * C ^ r * (Nat.factorial r : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r q (k * r) f

/-- Typed O-S E1--E4 test conditions; no continuum moment convergence
or positivity is manufactured by the definition. -/
structure OSSchwingerAxioms
    {Rot PosPoly : Type*}
    (G : OSTestGeometry Rot PosPoly) (H : SchwingerHierarchy) : Prop where
  normalization : ∀ f : JointTest 0, H.S 0 f = f 0
  E0prime : OS_E0prime H
  E1 : ∀ (r : ℕ) (R : Rot) (f : JointTest r),
    H.S r (G.rotate r R f) = H.S r f
  E1translations : ∀ (r : ℕ) (x : EuclideanSpace ℝ (Fin 4))
      (f : JointTest r),
    H.S r (G.translate r x f) = H.S r f
  E2 : ∀ p : PosPoly, G.positiveTime p →
    (G.reflectedPolynomialMoment H p p).im = 0 ∧
    0 ≤ (G.reflectedPolynomialMoment H p p).re
  E3 : ∀ (r : ℕ) (σ : Equiv.Perm (Fin r)) (f : JointTest r),
    H.S r (G.permute r σ f) = H.S r f
  E4 : ∀ (r s : ℕ) (f : JointTest r) (g : JointTest s),
    Tendsto (fun t : ℝ => H.S (r + s) (G.separate r s f g t))
      atTop (𝓝 (H.S r f * H.S s g))

/-- Exact published theorem is an EXTERNAL input, with its reconstructed
R0'--R5 Wightman data, correct Euclidean analytic-continuation
correspondence and uniqueness up to unitary equivalence.
No reconstructed field is inserted as a premise for the MODEL. -/
structure PublishedOSII {Rot PosPoly : Type*}
    (G : OSTestGeometry Rot PosPoly) where
  WightmanTheory : Type
  satisfies_R0prime_R5 : WightmanTheory → Prop
  euclideanBoundaryOf : WightmanTheory → SchwingerHierarchy → Prop
  vacuumUnitaryEquivalent : WightmanTheory → WightmanTheory → Prop
  Eprime_to_Rprime :
    ∀ H : SchwingerHierarchy, OSSchwingerAxioms G H →
      ∃ W : WightmanTheory,
        satisfies_R0prime_R5 W ∧ euclideanBoundaryOf W H
  uniqueness :
    ∀ (H : SchwingerHierarchy) (W W' : WightmanTheory),
      satisfies_R0prime_R5 W → satisfies_R0prime_R5 W' →
      euclideanBoundaryOf W H → euclideanBoundaryOf W' H →
      vacuumUnitaryEquivalent W W'

/-- Original #34, paper Theorem 17.9, registered with the *corrected*
published OS II E' -> R' interface. No theorem premise posits
a pre-existing physical reconstructed Wightman solution. -/
theorem original34_os_reconstruction_external_interface
    {Rot PosPoly : Type*}
    (G : OSTestGeometry Rot PosPoly)
    (Published : PublishedOSII G)
    (H : SchwingerHierarchy)
    (hE : OSSchwingerAxioms G H) :
    ∃ W : Published.WightmanTheory,
      Published.satisfies_R0prime_R5 W ∧
      Published.euclideanBoundaryOf W H ∧
      (∀ W' : Published.WightmanTheory,
        Published.satisfies_R0prime_R5 W' →
        Published.euclideanBoundaryOf W' H →
        Published.vacuumUnitaryEquivalent W W') := by
  obtain ⟨W, hW, hmatch⟩ := Published.Eprime_to_Rprime H hE
  refine ⟨W, hW, hmatch, ?_⟩
  intro W' hW' hmatch'
  exact Published.uniqueness H W W' hW hW' hmatch hmatch'

#print axioms original34_os_reconstruction_external_interface

end YMUIC.Original34
