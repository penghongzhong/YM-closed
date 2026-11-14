import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option autoImplicit false
namespace YMUIC.OSTensor
open LineDeriv

/-- A unit-bounded direction costs one derivative and no dimension constant. -/
theorem schwartz_directional_seminorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (v : E) (hv : ‖v‖ ≤ 1) (q m : ℕ) :
    SchwartzMap.seminorm ℂ q m (∂_{v} f) ≤ SchwartzMap.seminorm ℂ q (m + 1) f := by
  apply SchwartzMap.seminorm_le_bound ℂ q m _ (apply_nonneg _ _)
  intro x
  have hb : ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ :=
    norm_iteratedFDeriv_clm_apply_const
      ((SchwartzMap.fderivCLM ℂ E ℂ f).smooth _).contDiffAt le_rfl
  rw [norm_iteratedFDeriv_fderiv] at hb
  have h := hb.trans (mul_le_of_le_one_left (norm_nonneg _) hv)
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (f.le_seminorm ℂ q (m + 1) x)
end YMUIC.OSTensor
