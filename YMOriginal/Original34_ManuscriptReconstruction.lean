import YMOriginal.Original34_OSII_ExternalInterface

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original34

/-!
# C29 Original environment 34, paper Theorem 17.9, E' => R' (1975)

This is the original theorem's conditional OS reconstruction step:
S0 normalization, E0' on the full 4r Schwartz space, E1 translations
AND rotations, E2 positive-time reflection positivity, E3 bosonic
permutation symmetry and E4 cluster property.

The two-stage invocation is:
1. Assemble the SAME actual Schwinger hierarchy H's E0'--E4
   hypotheses (outputs of manuscript original 25, 28, 30, 31--33).
2. Apply the registered published 1975 OS-II E' => R' theorem.

No Wightman field or uniqueness is assumed as a Yang--Mills model
premise. The Published parameter is a classical external-theorem
interface, not a Lean axiom or a proof of the published theorem.

Actual physical interpretation still requires the geometric action
dictionary and model E0'; this does NOT close Original30.
-/

/-- Manuscript #34's explicit original input list; each part refers to
the SAME H and SAME geometric actions. The conclusion is absent from
the input fields. -/
structure Original34ManuscriptInputs
    {Rot PosPoly : Type*}
    (G : OSTestGeometry Rot PosPoly)
    (H : SchwingerHierarchy) : Prop where
  S0 : ∀ f : JointTest 0, H.S 0 f = f 0
  fromOriginal30_E0prime : OS_E0prime H
  fromOriginal31_E1_rotations :
    ∀ (r : ℕ) (R : Rot) (f : JointTest r),
      H.S r (G.rotate r R f) = H.S r f
  fromOriginal31_E1_translations :
    ∀ (r : ℕ) (x : EuclideanSpace ℝ (Fin 4))
      (f : JointTest r),
      H.S r (G.translate r x f) = H.S r f
  fromOriginal28_E2 :
    ∀ p : PosPoly, G.positiveTime p →
      (G.reflectedPolynomialMoment H p p).im = 0 ∧
      0 ≤ (G.reflectedPolynomialMoment H p p).re
  fromOriginal32_E3 :
    ∀ (r : ℕ) (σ : Equiv.Perm (Fin r)) (f : JointTest r),
      H.S r (G.permute r σ f) = H.S r f
  fromOriginal33_E4 :
    ∀ (r s : ℕ) (f : JointTest r) (g : JointTest s),
      Tendsto (fun t : ℝ =>
        H.S (r + s) (G.separate r s f g t))
        atTop (𝓝 (H.S r f * H.S s g))

/-- Input equivalence: corrected normalized OS II assumptions exactly
match the conditional manuscript E0'--E4 list. -/
theorem original34_manuscript_axioms_iff
    {Rot PosPoly : Type*}
    (G : OSTestGeometry Rot PosPoly)
    (H : SchwingerHierarchy) :
    Original34ManuscriptInputs G H ↔ OSSchwingerAxioms G H := by
  constructor
  · intro h
    exact ⟨h.S0, h.fromOriginal30_E0prime,
      h.fromOriginal31_E1_rotations,
      h.fromOriginal31_E1_translations,
      h.fromOriginal28_E2,
      h.fromOriginal32_E3, h.fromOriginal33_E4⟩
  · intro h
    exact ⟨h.normalization, h.E0prime, h.E1, h.E1translations,
      h.E2, h.E3, h.E4⟩

/-- C29 Theorem 17.9, exact conditional existence, original Schwinger
boundary-value identification and vacuum-unitary uniqueness. -/
theorem original34_manuscript_reconstruction
    {Rot PosPoly : Type*}
    (G : OSTestGeometry Rot PosPoly)
    (Published : PublishedOSII G)
    (H : SchwingerHierarchy)
    (h : Original34ManuscriptInputs G H) :
    ∃ W : Published.WightmanTheory,
      Published.satisfies_R0prime_R5 W ∧
      Published.euclideanBoundaryOf W H ∧
      (∀ W' : Published.WightmanTheory,
        Published.satisfies_R0prime_R5 W' →
        Published.euclideanBoundaryOf W' H →
        Published.vacuumUnitaryEquivalent W W') := by
  exact original34_os_reconstruction_external_interface G Published H
    ((original34_manuscript_axioms_iff G H).mp h)

#print axioms original34_manuscript_axioms_iff
#print axioms original34_manuscript_reconstruction

end YMUIC.Original34
