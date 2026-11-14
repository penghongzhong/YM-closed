import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original15Published

/-!
# Osterwalder--Seiler lattice positivity/transfer input

External source supplied by the user:
K. Osterwalder and E. Seiler, "Gauge Field Theories on a Lattice",
Annals of Physics 110 (1978), 440--471.

The paper proves physical positivity for the Euclidean lattice gauge
approximation and constructs a positive self-adjoint transfer matrix.
Lean does not re-prove that published construction.  We expose only the
two pieces used by the conditional I7 chain: positivity of the actual
transfer operator and normalization of the vacuum as its fixed vector.
-/

structure PublishedOsterwalderSeilerTransfer
    {κ : Type*}
    (V : κ → Type*)
    [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)]
    (Ω : ∀ k, V k)
    (T : ∀ k, V k →L[ℂ] V k) : Prop where
  positive : ∀ k, (T k).IsPositive
  vacuumFixed : ∀ k, T k (Ω k) = Ω k

theorem published_osterwalder_seiler_transfer_inputs
    {κ : Type*}
    (V : κ → Type*)
    [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)]
    (Ω : ∀ k, V k)
    (T : ∀ k, V k →L[ℂ] V k)
    (OS : PublishedOsterwalderSeilerTransfer V Ω T) :
    (∀ k, (T k).IsPositive) ∧ (∀ k, T k (Ω k) = Ω k) :=
  ⟨OS.positive, OS.vacuumFixed⟩

#print axioms published_osterwalder_seiler_transfer_inputs

end YMUIC.Original15Published
