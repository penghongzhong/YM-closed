import YM.Wilson.SourceDirection

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- The true Schwartz weighted evaluation estimate; no localization
radius or compact-support assumption is needed. -/
theorem schwartz_weighted_point_bound
    (q : ℕ) (f : SchwartzMap Space4 ℂ) (x : Space4) :
    (1 + ‖x‖ ^ q) * ‖f x‖ ≤
      SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ q 0 f := by
  have h0 := f.norm_le_seminorm ℂ x
  have hq := f.norm_pow_mul_le_seminorm ℂ q x
  nlinarith

/-- Genuine SU(2) plaquette source, weighted by its physical position.
This is a *pointwise* bound which includes the spatial Schwartz decay. -/
theorem wilson_weighted_point_bound
    {P : Type*} (q : ℕ)
    (U : P → YMUICV128.Section03.SU2) (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) (p : P) :
    (1 + ‖position p‖ ^ q) * ‖wilsonPlaquetteDirection U position f p‖ ≤
      4 * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) := by
  obtain ⟨hW0, hW4⟩ := YMUICV128.Section03.wilsonRoot_bounds (U p)
  have hW : ‖(YMUICV128.Section03.wilsonRoot (U p) : ℂ)‖ ≤ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0]
    exact hW4
  have hpoint :
      ‖wilsonPlaquetteDirection U position f p‖ ≤
        4 * ‖f (position p)‖ := by
    calc
      _ = ‖f (position p)‖ *
          ‖(YMUICV128.Section03.wilsonRoot (U p) : ℂ)‖ := by
            simp only [wilsonPlaquetteDirection, norm_mul]
      _ ≤ ‖f (position p)‖ * 4 :=
        mul_le_mul_of_nonneg_left hW (norm_nonneg _)
      _ = 4 * ‖f (position p)‖ := by ring
  have hp : 0 ≤ 1 + ‖position p‖ ^ q := by positivity
  calc
    (1 + ‖position p‖ ^ q) * ‖wilsonPlaquetteDirection U position f p‖ ≤
        (1 + ‖position p‖ ^ q) * (4 * ‖f (position p)‖) :=
          mul_le_mul_of_nonneg_left hpoint hp
    _ = 4 * ((1 + ‖position p‖ ^ q) * ‖f (position p)‖) := by ring
    _ ≤ 4 * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) :=
          mul_le_mul_of_nonneg_left
            (schwartz_weighted_point_bound q f (position p)) (by norm_num)

/-- The actual finite Wilson plaquette sum with arbitrary source smearing
weights. The physical lattice-volume normalization is encoded only by
`weight`, not inserted as an unproved universal constant. -/
def wilsonWeightedSmearing {P : Type*} [Fintype P]
    (weight : P → ℂ)
    (U : P → YMUICV128.Section03.SU2) (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) : ℂ :=
  ∑ p : P, weight p * wilsonPlaquetteDirection U position f p

/-- Weighted lattice cubature criterion for volume-uniform source bounds:
a single geometric sum of source weights, with the genuine Schwartz
decay factor, controls the actual whole finite-volume Wilson smearing. -/
theorem wilson_weighted_smearing_bound
    {P : Type*} [Fintype P]
    (weight : P → ℂ)
    (U : P → YMUICV128.Section03.SU2) (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) (q : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hweight : (∑ p : P,
      ‖weight p‖ / (1 + ‖position p‖ ^ q)) ≤ C) :
    ‖wilsonWeightedSmearing weight U position f‖ ≤
      4 * C * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) := by
  let S : ℝ := SchwartzMap.seminorm ℂ 0 0 f +
    SchwartzMap.seminorm ℂ q 0 f
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hsingle (p : P) :
      ‖weight p * wilsonPlaquetteDirection U position f p‖ ≤
        (‖weight p‖ / (1 + ‖position p‖ ^ q)) * (4 * S) := by
    have hp : 0 < 1 + ‖position p‖ ^ q := by positivity
    have hw := wilson_weighted_point_bound q U position f p
    have hdiv : ‖wilsonPlaquetteDirection U position f p‖ ≤
        4 * S / (1 + ‖position p‖ ^ q) := by
      apply (le_div_iff₀ hp).mpr
      calc
        ‖wilsonPlaquetteDirection U position f p‖ *
            (1 + ‖position p‖ ^ q) =
            (1 + ‖position p‖ ^ q) *
              ‖wilsonPlaquetteDirection U position f p‖ := by ring
        _ ≤ 4 * S := by simpa only [S] using hw
    calc
      ‖weight p * wilsonPlaquetteDirection U position f p‖ =
          ‖weight p‖ * ‖wilsonPlaquetteDirection U position f p‖ := norm_mul _ _
      _ ≤ ‖weight p‖ * (4 * S / (1 + ‖position p‖ ^ q)) :=
        mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
      _ = (‖weight p‖ / (1 + ‖position p‖ ^ q)) * (4 * S) := by ring
  calc
    ‖wilsonWeightedSmearing weight U position f‖ ≤
        ∑ p : P, ‖weight p * wilsonPlaquetteDirection U position f p‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ p : P,
        (‖weight p‖ / (1 + ‖position p‖ ^ q)) * (4 * S) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hsingle p
    _ = (∑ p : P, ‖weight p‖ / (1 + ‖position p‖ ^ q)) * (4 * S) := by
      rw [Finset.sum_mul]
    _ ≤ C * (4 * S) := mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = 4 * C * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) := by dsimp [S]; ring

/-- The same fixed weighted-quadrature bound for all physical UV
cutoffs and volumes, with no restriction on the number of plaquettes. -/
theorem wilson_weighted_smearing_all_regulators
    {Regulator : Type*} (P : Regulator → Type*)
    [∀ i, Fintype (P i)]
    (weight : (i : Regulator) → P i → ℂ)
    (U : (i : Regulator) → P i → YMUICV128.Section03.SU2)
    (position : (i : Regulator) → P i → Space4)
    (f : SchwartzMap Space4 ℂ) (q : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hweight : ∀ i, (∑ p : P i,
      ‖weight i p‖ / (1 + ‖position i p‖ ^ q)) ≤ C) :
    ∀ i, ‖wilsonWeightedSmearing (weight i) (U i) (position i) f‖ ≤
      4 * C * (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ q 0 f) :=
  fun i => wilson_weighted_smearing_bound (weight i) (U i) (position i)
    f q C hC (hweight i)

end YMUIC.Wilson
