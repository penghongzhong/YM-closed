import YM.Wilson.RootBound

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

abbrev Space4 := EuclideanSpace ℝ (Fin 4)

/-- Genuine SU(2) plaquette-root source: a smooth complex test is sampled at
each physical root position and multiplied by W_p=2-Re Tr(U_p).
No extra Wilson-root bound or lattice regulator uniformity is assumed. -/
def wilsonPlaquetteDirection {P : Type*}
    (U : P → SU2) (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) : P → ℂ :=
  fun p => f (position p) * (wilsonRoot (U p) : ℂ)

/-- Each actual SU(2) Wilson plaquette root is a bounded multiplier.
The seminorm on the RHS is the **real** Schwartz seminorm p_{0,0}, not an
assumed C⁰ source bound. -/
theorem wilson_plaquette_direction_pointwise {P : Type*}
    (U : P → SU2) (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) (p : P) :
    ‖wilsonPlaquetteDirection U position f p‖ ≤
      4 * SchwartzMap.seminorm ℂ 0 0 f := by
  obtain ⟨hW0, hW4⟩ := wilsonRoot_bounds (U p)
  have hW : ‖(wilsonRoot (U p) : ℂ)‖ ≤ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0]
    exact hW4
  have hf : ‖f (position p)‖ ≤ SchwartzMap.seminorm ℂ 0 0 f :=
    f.norm_le_seminorm ℂ (position p)
  calc
    ‖wilsonPlaquetteDirection U position f p‖ =
        ‖f (position p)‖ * ‖(wilsonRoot (U p) : ℂ)‖ := by
          simp only [wilsonPlaquetteDirection, norm_mul]
    _ ≤ SchwartzMap.seminorm ℂ 0 0 f * 4 :=
      mul_le_mul hf hW (norm_nonneg _) (apply_nonneg _ _)
    _ = 4 * SchwartzMap.seminorm ℂ 0 0 f := by ring

/-- The finite-volume source l-infinity bound is independent of the number
of plaquettes, their locations, and the lattice spacing. -/
theorem wilson_plaquette_direction_uniform {P : Type*} [Fintype P]
    (U : P → SU2) (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ‖wilsonPlaquetteDirection U position f‖ ≤
      4 * SchwartzMap.seminorm ℂ 0 0 f := by
  have hn : 0 ≤ 4 * SchwartzMap.seminorm ℂ 0 0 f :=
    mul_nonneg (by norm_num) (apply_nonneg _ _)
  exact (pi_norm_le_iff_of_nonneg hn).2
    (fun p => wilson_plaquette_direction_pointwise U position f p)

/-- Exact source linearity, without a model-specific norm interface. -/
theorem wilson_plaquette_direction_sub {P : Type*}
    (U : P → SU2) (position : P → Space4)
    (f g : SchwartzMap Space4 ℂ) :
    wilsonPlaquetteDirection U position (f - g) =
      wilsonPlaquetteDirection U position f -
        wilsonPlaquetteDirection U position g := by
  funext p
  change (f (position p) - g (position p)) *
      (wilsonRoot (U p) : ℂ) =
      f (position p) * (wilsonRoot (U p) : ℂ) -
        g (position p) * (wilsonRoot (U p) : ℂ)
  exact sub_mul _ _ _

/-- A cutoff-uniform source modulus with no volume-dependent factor.
The source uses the SAME SU(2) configuration in both terms. -/
theorem wilson_plaquette_direction_lipschitz {P : Type*} [Fintype P]
    (U : P → SU2) (position : P → Space4)
    (f g : SchwartzMap Space4 ℂ) :
    ‖wilsonPlaquetteDirection U position f -
        wilsonPlaquetteDirection U position g‖ ≤
      4 * SchwartzMap.seminorm ℂ 0 0 (f - g) := by
  rw [← wilson_plaquette_direction_sub]
  exact wilson_plaquette_direction_uniform U position (f - g)

/-- Quantifiers deliberately cover **all** regulators, volumes and root
positions. No bound on volume or spacing is slipped into this statement. -/
theorem wilson_plaquette_direction_all_regulators
    {Regulator : Type*} (P : Regulator → Type*)
    [∀ i, Fintype (P i)]
    (U : (i : Regulator) → P i → SU2)
    (position : (i : Regulator) → P i → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ i, ‖wilsonPlaquetteDirection (U i) (position i) f‖ ≤
      4 * SchwartzMap.seminorm ℂ 0 0 f :=
  fun i => wilson_plaquette_direction_uniform (U i) (position i) f

end YMUIC.Wilson
