import YMConditional.Original25_RotationMatching

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace YMUIC.EuclideanCovariance
open YMUIC.RotationMatching
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Geometric translation of the SAME continuum source field. -/
def translateField (a : Space4) (f : Space4 → V) : Space4 → V :=
  fun x => f (x - a)

def translateFamily {n : ℕ} (a : Space4)
    (f : Fin n → Space4 → V) : Fin n → Space4 → V :=
  fun j => translateField a (f j)

/-- A Euclidean motion is rotation followed by translation, with tensor
representation rho(R), not a rotation of one fixed cubic regulator. -/
def euclideanFamily {n : ℕ} (a : Space4) (R : Rotation4)
    (rho : V →ₗ[ℂ] V) (f : Fin n → Space4 → V) :
    Fin n → Space4 → V :=
  fun j x => rho (f j (R.symm (x - a)))

theorem euclideanFamily_eq_translation_rotation {n : ℕ}
    (a : Space4) (R : Rotation4) (rho : V →ₗ[ℂ] V)
    (f : Fin n → Space4 → V) :
    euclideanFamily a R rho f = translateFamily a (rotateFamily R rho f) := by
  rfl

omit [AddCommGroup V] [Module ℂ V] in
/-- Lattice translation is exact only at regulator-dependent admissible
translations t_i. The separate SAME-net identification with continuum
translation by a is an explicit model-level prior hypothesis, never obtained
by asserting arbitrary real-translation symmetry on a fixed lattice. -/
theorem translated_limit_from_lattice_relabel
    {ι : Type*} {l : Filter ι} [l.NeBot] {n : ℕ}
    (a : Space4) (t : ι → Space4)
    (f : Fin n → Space4 → V)
    (cutoff : ι → (Fin n → Space4 → V) → ℂ)
    (S : (Fin n → Space4 → V) → ℂ)
    (hfinite : ∀ᶠ i in l,
       cutoff i (translateFamily (t i) f) = cutoff i f)
    (horiginal : Tendsto (fun i => cutoff i f) l (𝓝 (S f)))
    (hjointshift : Tendsto (fun i => cutoff i (translateFamily a f))
       l (𝓝 (S (translateFamily a f))))
    (hsourceerror : Tendsto
      (fun i => cutoff i (translateFamily (t i) f) -
        cutoff i (translateFamily a f)) l (𝓝 (0 : ℂ))) :
    S (translateFamily a f) = S f := by
  have htrans : Tendsto (fun i => cutoff i (translateFamily (t i) f)) l
      (𝓝 (S (translateFamily a f))) := by
    have hh := hsourceerror.add hjointshift
    simpa only [sub_add_cancel, zero_add] using hh
  have h : Tendsto (fun i => cutoff i (translateFamily (t i) f)) l
      (𝓝 (S f)) := horiginal.congr' (hfinite.mono (fun _ h => h.symm))
  exact tendsto_nhds_unique htrans h

end YMUIC.EuclideanCovariance
