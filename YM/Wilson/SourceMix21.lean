import YM.Wilson.SourceDirection

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

abbrev RootFiber21 := Fin 21

/-- The actual 21-root source vector after a finite complex source-cocycle
matrix. The matrix acts on the same physical SU(2) root configuration;
the action is an explicit finite sum, not an assumed source isomorphism. -/
def mixedWilsonDirection
    (B : RootFiber21 → RootFiber21 → ℂ)
    (U : RootFiber21 → SU2) (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) : RootFiber21 → ℂ :=
  fun α => ∑ j : RootFiber21,
    B j α * wilsonPlaquetteDirection U position f j

/-- The correct *actual* finite-dimensional C² source dictionary begins with
this bound. Its only unproved model input for regulator uniformity is the
column ℓ¹ amplification of the cumulative source matrix B. -/
theorem mixed_wilson_direction_pointwise
    (B : RootFiber21 → RootFiber21 → ℂ)
    (U : RootFiber21 → SU2) (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) (α : RootFiber21) :
    ‖mixedWilsonDirection B U position f α‖ ≤
      (∑ j : RootFiber21, ‖B j α‖) *
        (4 * SchwartzMap.seminorm ℂ 0 0 f) := by
  have hs :
      ‖∑ j : RootFiber21, B j α *
        wilsonPlaquetteDirection U position f j‖ ≤
        ∑ j : RootFiber21, ‖B j α *
          wilsonPlaquetteDirection U position f j‖ :=
    norm_sum_le _ _
  calc
    ‖mixedWilsonDirection B U position f α‖ ≤
        ∑ j : RootFiber21, ‖B j α *
          wilsonPlaquetteDirection U position f j‖ := by
            simpa only [mixedWilsonDirection] using hs
    _ = ∑ j : RootFiber21,
          ‖B j α‖ * ‖wilsonPlaquetteDirection U position f j‖ := by
            simp only [norm_mul]
    _ ≤ ∑ j : RootFiber21,
          ‖B j α‖ * (4 * SchwartzMap.seminorm ℂ 0 0 f) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left
              (wilson_plaquette_direction_pointwise U position f j) (norm_nonneg _)
    _ = (∑ j : RootFiber21, ‖B j α‖) *
          (4 * SchwartzMap.seminorm ℂ 0 0 f) := by
            rw [Finset.sum_mul]

/-- The exact missing **uniform 21×21 renormalized source norm** is
a column-sum estimate, not invertibility or reflection positivity of B.
Under that explicit bound, Wilson-root source smearing is genuinely
uniform in the lattice background and plaquette locations. -/
theorem mixed_wilson_direction_uniform
    (B : RootFiber21 → RootFiber21 → ℂ)
    (U : RootFiber21 → SU2) (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) (K : ℝ)
    (hK : 0 ≤ K)
    (hcolumn : ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖B j α‖) ≤ K) :
    ‖mixedWilsonDirection B U position f‖ ≤
      4 * K * SchwartzMap.seminorm ℂ 0 0 f := by
  have hp : 0 ≤ SchwartzMap.seminorm ℂ 0 0 f := apply_nonneg _ _
  have hrhs : 0 ≤ 4 * K * SchwartzMap.seminorm ℂ 0 0 f := by positivity
  apply (pi_norm_le_iff_of_nonneg hrhs).2
  intro α
  calc
    ‖mixedWilsonDirection B U position f α‖ ≤
        (∑ j : RootFiber21, ‖B j α‖) *
        (4 * SchwartzMap.seminorm ℂ 0 0 f) :=
          mixed_wilson_direction_pointwise B U position f α
    _ ≤ K * (4 * SchwartzMap.seminorm ℂ 0 0 f) :=
      mul_le_mul_of_nonneg_right (hcolumn α)
        (mul_nonneg (by norm_num) hp)
    _ = 4 * K * SchwartzMap.seminorm ℂ 0 0 f := by ring

/-- The fixed-root estimate is uniform over every UV regulator and volume
provided the SAME model supplies a regulator-uniform column sum. No I7,
Wilson source norm, lattice size, or renormalization hypothesis is hidden. -/
theorem mixed_wilson_direction_all_regulators
    {Regulator : Type*}
    (B : Regulator → RootFiber21 → RootFiber21 → ℂ)
    (U : Regulator → RootFiber21 → SU2)
    (position : Regulator → RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) (K : ℝ)
    (hK : 0 ≤ K)
    (hcolumn : ∀ i α, (∑ j : RootFiber21, ‖B i j α‖) ≤ K) :
    ∀ i, ‖mixedWilsonDirection (B i) (U i) (position i) f‖ ≤
      4 * K * SchwartzMap.seminorm ℂ 0 0 f :=
  fun i => mixed_wilson_direction_uniform (B i) (U i) (position i)
    f K hK (hcolumn i)

end YMUIC.Wilson
