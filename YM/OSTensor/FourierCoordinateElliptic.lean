import YM.OSTensor.FourierCoordinateDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace YMUIC.OSTensor
open MeasureTheory UnitAddTorus
noncomputable local instance fourierCoordinateEllipticMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance fourierCoordinateEllipticProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The coordinate operator (1-∂ᵢ²)² has an everywhere positive Fourier multiplier. -/
theorem fourier_coordinate_elliptic {n : ℕ} (i : Fin (n + 1))
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hd : ∀ j < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => F j (i.insertNth (y : UnitAddCircle) z))
        (F (j + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (k : Fin (n + 1) → ℤ) :
    mFourierCoeff (F 0 - (2 : ℂ) • F 2 + F 4) k =
      ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2) ^ 2 : ℝ) * mFourierCoeff (F 0) k := by
  have hj (j : ℕ) (h : j ≤ 4) : mFourierCoeff (F j) k =
      (2 * Real.pi * Complex.I * k i) ^ j * mFourierCoeff (F 0) k := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [fourier_coordinate_derivative i (F j) (F (j + 1)) (hd j (by omega)) k,
        ih (by omega), pow_succ']
      ring
  have hI (j : ℕ) : Integrable (fun x => mFourier (-k) x * F j x) :=
    (by fun_prop : Continuous (fun x => mFourier (-k) x * F j x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : mFourierCoeff (F 0 - (2 : ℂ) • F 2 + F 4) k =
      mFourierCoeff (F 0) k - 2 * mFourierCoeff (F 2) k + mFourierCoeff (F 4) k := by
    simp only [mFourierCoeff, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, smul_eq_mul, mul_add, mul_sub]
    simp_rw [mul_left_comm _ (2 : ℂ)]
    have ha := integral_add ((hI 0).sub ((hI 2).const_mul 2)) (hI 4)
    have hb := integral_sub (hI 0) ((hI 2).const_mul 2)
    simp only [Pi.sub_apply] at ha
    calc
      _ = _ := ha
      _ = _ := by rw [hb, integral_const_mul]
  rw [he, hj 2 (by decide), hj 4 (by decide)]
  push_cast
  ring_nf
  simp [Complex.I_sq]
end YMUIC.OSTensor
