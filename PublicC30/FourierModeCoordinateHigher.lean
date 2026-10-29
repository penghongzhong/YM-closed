import PublicC30.FourierModeCoordinate

set_option autoImplicit false

namespace YMUIC.OSTensor
open UnitAddTorus

/-- Every coefficient of the actual coordinate-derivative chain of a Fourier
atom is explicitly computed. In particular this supplies orders 0,1,2,3,4
needed for a C² source estimate and the fourth-order elliptic operator. -/
theorem fourier_mode_coordinate_iterated_hasDerivAt {n : ℕ}
    (k : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (z : UnitAddTorus (Fin n)) (j : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j *
          mFourier k (i.insertNth (y : UnitAddCircle) z))
      ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ (j + 1) *
        mFourier k (i.insertNth (x : UnitAddCircle) z)) x := by
  simpa only [pow_succ, mul_assoc] using
    (fourier_mode_coordinate_hasDerivAt k i z x).const_mul
      ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j)

/-- Fourier atoms have pointwise norm one, even for zero frequencies. -/
theorem fourier_mode_coordinate_norm_one {n : ℕ}
    (k : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (z : UnitAddTorus (Fin n)) (x : ℝ) :
    ‖mFourier k (i.insertNth (x : UnitAddCircle) z)‖ = 1 := by
  change ‖∏ j : Fin (n + 1),
    fourier (k j) ((i.insertNth (x : UnitAddCircle) z) j)‖ = 1
  rw [norm_prod]
  simp only [fourier_apply, Circle.norm_coe, Finset.prod_const_one]

end YMUIC.OSTensor
