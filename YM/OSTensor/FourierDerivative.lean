import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false
namespace YMUIC.OSTensor
open AddCircle MeasureTheory

/-- Integration by parts for actual unit-circle coefficients, including the
zero frequency. The derivative is taken on the periodic real lift. -/
theorem fourier_derivative (f g : C(UnitAddCircle, ℂ))
    (hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : UnitAddCircle)) (g (x : UnitAddCircle)) x)
    (k : ℤ) :
    fourierCoeff g k = (2 * Real.pi * Complex.I * k) * fourierCoeff f k := by
  have he : ((1 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) := by
    simpa only [zero_add, AddCircle.coe_zero] using AddCircle.coe_add_period (1 : ℝ) 0
  have hχ : Continuous (fun x : ℝ => fourier (-k) (x : UnitAddCircle)) :=
    (fourier (-k)).continuous.comp (AddCircle.continuous_mk' 1)
  have hg : Continuous (fun x : ℝ => g (x : UnitAddCircle)) :=
    g.continuous.comp (AddCircle.continuous_mk' 1)
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    hχ.continuousOn
    (f.continuous.comp (AddCircle.continuous_mk' 1)).continuousOn
    (fun x _ => hasDerivAt_fourier_neg (1 : ℝ) k x)
    (fun x _ => hd x)
    ((continuous_const.mul hχ).intervalIntegrable 0 1)
    (hg.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one, div_one] at hb
  change (∫ x in (0 : ℝ)..1, fourier (-k) (x : UnitAddCircle) * g (x : UnitAddCircle)) =
    fourier (-k) ((1 : ℝ) : UnitAddCircle) * f ((1 : ℝ) : UnitAddCircle) -
      fourier (-k) ((0 : ℝ) : UnitAddCircle) * f ((0 : ℝ) : UnitAddCircle) -
      ∫ x in (0 : ℝ)..1, (-2 * Real.pi * Complex.I * k) *
        fourier (-k) (x : UnitAddCircle) * f (x : UnitAddCircle) at hb
  rw [he, AddCircle.coe_zero, sub_self] at hb
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at hb
  rw [fourierCoeff_eq_intervalIntegral g k 0, fourierCoeff_eq_intervalIntegral f k 0]
  simp only [zero_add, div_self (one_ne_zero : (1 : ℝ) ≠ 0), one_smul, smul_eq_mul]
  calc
    _ = _ := hb
    _ = _ := by ring

end YMUIC.OSTensor
