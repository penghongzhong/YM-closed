import YM.OSTensor.FourierCoordinateFubini
import YM.OSTensor.FourierDerivative

set_option autoImplicit false
namespace YMUIC.OSTensor
open MeasureTheory UnitAddTorus
noncomputable local instance fourierCoordinateDerivativeMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Actual coordinate derivatives multiply multivariate Fourier coefficients by 2πikᵢ. -/
theorem fourier_coordinate_derivative {n : ℕ} (i : Fin (n + 1))
    (f g : C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hd : ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f (i.insertNth (y : UnitAddCircle) z))
        (g (i.insertNth (x : UnitAddCircle) z)) x)
    (k : Fin (n + 1) → ℤ) :
    mFourierCoeff g k = (2 * Real.pi * Complex.I * k i) * mFourierCoeff f k := by
  rw [fourier_coordinate_fubini i g k, fourier_coordinate_fubini i f k,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  let fs : C(UnitAddCircle, ℂ) := ⟨fun t => f (i.insertNth t z),
    f.continuous.comp (Continuous.finInsertNth (A := fun _ => UnitAddCircle) i continuous_id continuous_const)⟩
  let gs : C(UnitAddCircle, ℂ) := ⟨fun t => g (i.insertNth t z),
    g.continuous.comp (Continuous.finInsertNth (A := fun _ => UnitAddCircle) i continuous_id continuous_const)⟩
  have h := fourier_derivative fs gs (hd z) (k i)
  change _ * fourierCoeff gs (k i) = _ * (_ * fourierCoeff fs (k i))
  rw [h]
  ring
end YMUIC.OSTensor
