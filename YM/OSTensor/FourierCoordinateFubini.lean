import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false
namespace YMUIC.OSTensor
open MeasureTheory UnitAddTorus
noncomputable local instance fourierCoordinateFubiniMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance fourierCoordinateFubiniProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Isolate any coordinate of the actual multivariate Fourier integral. -/
theorem fourier_coordinate_fubini {n : ℕ} (i : Fin (n + 1))
    (f : C(UnitAddTorus (Fin (n + 1)), ℂ)) (k : Fin (n + 1) → ℤ) :
    mFourierCoeff f k = ∫ z : UnitAddTorus (Fin n),
      (∏ j, fourier (-(k (i.succAbove j))) (z j)) *
        fourierCoeff (fun t : UnitAddCircle => f (i.insertNth t z)) (k i) := by
  let H : UnitAddTorus (Fin (n + 1)) → ℂ := fun x => mFourier (-k) x * f x
  have hc : Continuous H := by fun_prop
  have hI : Integrable H := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace H)
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)) i).symm
  have he : (∫ x, H x) = ∫ p : UnitAddCircle × UnitAddTorus (Fin n),
      H (i.insertNth p.1 p.2) := by
    exact (hmp.integral_comp' H).symm
  change (∫ x, H x) = _
  rw [he]
  change (∫ p, H (i.insertNth p.1 p.2) ∂(volume.prod volume)) = _
  rw [integral_prod_symm]
  · apply integral_congr_ae
    filter_upwards [] with z
    simp only [H, mFourier, ContinuousMap.coe_mk, Pi.neg_apply]
    simp_rw [i.prod_univ_succAbove]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    simp_rw [mul_assoc, mul_comm (fourier (-(k i)) _), mul_assoc]
    rw [integral_const_mul]
    simp only [fourierCoeff, smul_eq_mul, mul_comm]
    rfl
  · exact hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hI
end YMUIC.OSTensor
