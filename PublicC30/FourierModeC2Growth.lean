import PublicC30.FourierModeCoordinateHigher

set_option autoImplicit false

namespace YMUIC.OSTensor
open UnitAddTorus

/-- The precise norm of the j-th real coordinate derivative of an actual
multidimensional Fourier character; valid for every frequency and order. -/
theorem fourier_mode_coordinate_iterated_norm {n : ℕ}
    (k : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (z : UnitAddTorus (Fin n)) (j : ℕ) (x : ℝ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j *
      mFourier k (i.insertNth (x : UnitAddCircle) z)‖ =
    ‖2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)‖ ^ j := by
  rw [norm_mul, norm_pow, fourier_mode_coordinate_norm_one, mul_one]

/-- The exact real frequency norm of one coordinate derivative multiplier. -/
theorem fourier_mode_frequency_norm (k : ℤ) :
    ‖2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)‖ =
      2 * Real.pi * |(k : ℝ)| := by
  calc
    _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ *
          ‖Complex.I‖ * ‖(k : ℂ)‖ := by
          rw [norm_mul, norm_mul, norm_mul]
    _ = _ := by
          simp [Complex.norm_real, Complex.norm_intCast, Complex.norm_I,
            Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]

/-- The actual zero, first and second partial derivative of a Fourier mode
obeys a single quadratic frequency bound with a constant independent of k. -/
theorem fourier_mode_coordinate_c2_bound {n : ℕ}
    (k : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (z : UnitAddTorus (Fin n)) (j : ℕ) (hj : j ≤ 2) (x : ℝ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j *
      mFourier k (i.insertNth (x : UnitAddCircle) z)‖ ≤
      (2 * Real.pi) ^ 2 * (1 + |(k i : ℝ)|) ^ 2 := by
  rw [fourier_mode_coordinate_iterated_norm, fourier_mode_frequency_norm]
  have ht : 0 ≤ (2 * Real.pi * |(k i : ℝ)|) := by positivity
  have hjbound : (2 * Real.pi * |(k i : ℝ)|) ^ j ≤
      (1 + 2 * Real.pi * |(k i : ℝ)|) ^ 2 := by
    interval_cases j <;> simp [pow_two] <;> nlinarith
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have habs : 0 ≤ |(k i : ℝ)| := abs_nonneg _
  have hb : 1 + 2 * Real.pi * |(k i : ℝ)| ≤
      (2 * Real.pi) * (1 + |(k i : ℝ)|) := by nlinarith
  calc
    _ ≤ (1 + 2 * Real.pi * |(k i : ℝ)|) ^ 2 := hjbound
    _ ≤ ((2 * Real.pi) * (1 + |(k i : ℝ)|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    _ = _ := by ring

end YMUIC.OSTensor
