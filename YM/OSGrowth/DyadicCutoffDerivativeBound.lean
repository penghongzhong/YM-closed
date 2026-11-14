import YM.OSGrowth.DyadicCutoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace YMUIC.OSGrowth

noncomputable def baseCutoffSchwartz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E] : SchwartzMap E ℝ :=
  (dyadicCutoff (E := E) 0).hasCompactSupport.toSchwartzMap
    (dyadicCutoff (E := E) 0).contDiff

/-- Exact rescaling of one fixed bump controls every cutoff derivative. -/
theorem dyadic_cutoff_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E] (n m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (dyadicCutoff (E := E) n) x‖ ≤
      SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E)) / (2 : ℝ) ^ (n * m) := by
  have hfun : (dyadicCutoff (E := E) n : E → ℝ) =
      fun y => dyadicCutoff (E := E) 0 (((2 : ℝ) ^ n)⁻¹ • y) := by
    funext y
    simp [ContDiffBump.apply, dyadicCutoff, pow_succ]
  rw [hfun, iteratedFDeriv_comp_const_smul _ (dyadicCutoff (E := E) 0).contDiff]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
    (baseCutoffSchwartz (E := E)) m (((2 : ℝ) ^ n)⁻¹ • x)
  change ‖iteratedFDeriv ℝ m (dyadicCutoff (E := E) 0) (((2 : ℝ) ^ n)⁻¹ • x)‖ ≤
    SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E)) at hb
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (((2 : ℝ) ^ n)⁻¹) ^ m)
  simpa [inv_pow, div_eq_mul_inv, mul_comm, pow_mul] using hm

end YMUIC.OSGrowth
