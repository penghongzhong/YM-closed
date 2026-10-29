import YM.OSTensor.FourierCoordinateFubini

set_option autoImplicit false

namespace YMUIC.OSTensor
open UnitAddTorus

/-- An actual multivariate Fourier atom, restricted to one real coordinate,
factorizes into one circle character and the unchanged remaining characters. -/
theorem fourier_mode_coordinate_eq {n : ℕ}
    (k : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (z : UnitAddTorus (Fin n)) (x : ℝ) :
    mFourier k (i.insertNth (x : UnitAddCircle) z) =
      fourier (k i) (x : UnitAddCircle) *
        ∏ j : Fin n, fourier (k (i.succAbove j)) (z j) := by
  change (∏ j : Fin (n + 1),
    fourier (k j) ((i.insertNth (x : UnitAddCircle) z) j)) = _
  rw [i.prod_univ_succAbove]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- The real-coordinate derivative of the actual torus Fourier atom. -/
theorem fourier_mode_coordinate_hasDerivAt {n : ℕ}
    (k : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (z : UnitAddTorus (Fin n)) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => mFourier k (i.insertNth (y : UnitAddCircle) z))
      ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) *
        mFourier k (i.insertNth (x : UnitAddCircle) z)) x := by
  have h := ((hasDerivAt_fourier (1 : ℝ) (k i) x).mul_const
    (∏ j : Fin n, fourier (k (i.succAbove j)) (z j)))
  simpa only [fourier_mode_coordinate_eq, div_one, mul_assoc] using h

end YMUIC.OSTensor
