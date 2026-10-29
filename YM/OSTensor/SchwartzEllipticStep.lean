import YM.OSTensor.SchwartzIteratedDirectionalSeminorm

set_option autoImplicit false
namespace YMUIC.OSTensor
open LineDeriv

/-- The actual coordinate operator (1-∂ᵥ²)² on Schwartz space. -/
noncomputable def schwartzEllipticStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f - (2 : ℂ) • ((lineDerivOp v)^[2] f) + ((lineDerivOp v)^[4] f)

/-- The fourth-order operator costs exactly the three indicated derivative seminorms. -/
theorem schwartz_elliptic_step_seminorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (v : E) (hv : ‖v‖ ≤ 1) (q m : ℕ) :
    SchwartzMap.seminorm ℂ q m (schwartzEllipticStep v f) ≤
      SchwartzMap.seminorm ℂ q m f + 2 * SchwartzMap.seminorm ℂ q (m + 2) f +
        SchwartzMap.seminorm ℂ q (m + 4) f := by
  let p : Seminorm ℂ (SchwartzMap E ℂ) := SchwartzMap.seminorm ℂ q m
  have ha := map_add_le_add p (f - (2 : ℂ) • ((lineDerivOp v)^[2] f)) ((lineDerivOp v)^[4] f)
  have hb := map_sub_le_add p f ((2 : ℂ) • ((lineDerivOp v)^[2] f))
  have hc : p ((2 : ℂ) • ((lineDerivOp v)^[2] f)) = 2 * p ((lineDerivOp v)^[2] f) := by
    simp only [map_smul_eq_mul, Complex.norm_ofNat]
  have h2 := schwartz_iterated_directional_seminorm f v hv q m 2
  have h4 := schwartz_iterated_directional_seminorm f v hv q m 4
  change p (schwartzEllipticStep v f) ≤ _
  rw [hc] at hb
  dsimp [schwartzEllipticStep, p] at *
  linarith
end YMUIC.OSTensor
