import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false
namespace YMUIC.OSTensor
open MeasureTheory UnitAddTorus
noncomputable local instance fourierMultivariateBoundMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance fourierMultivariateBoundProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Normalized multivariate Fourier coefficients are bounded by the supremum norm. -/
theorem fourier_multivariate_bound {d : Type*} [Fintype d]
    (f : C(UnitAddTorus d, ℂ)) (k : d → ℤ) : ‖mFourierCoeff f k‖ ≤ ‖f‖ := by
  have hb (x : UnitAddTorus d) : ‖mFourier (-k) x • f x‖ ≤ ‖f‖ := by
    rw [norm_smul]
    have hχ : ‖mFourier (-k) x‖ ≤ (1 : ℝ) := by
      simpa only [mFourier_norm] using (mFourier (-k)).norm_coe_le_norm x
    exact (mul_le_mul hχ (f.norm_coe_le_norm x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simpa only [mFourierCoeff, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus d)))
      (Filter.Eventually.of_forall hb))
end YMUIC.OSTensor
