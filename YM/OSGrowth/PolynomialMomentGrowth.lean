import YM.OSGrowth.PolynomialRadiusBound

open Metric Set

namespace YMUIC.OSGrowth

/-- The local moment estimate is polynomial of degree `r` in the logarithmic
bound `A`. This removes the exponential-in-volume loss of the half-radius bound. -/
theorem local_moment_polynomial_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : E → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hanalytic : AnalyticOnNhd ℂ W (ball 0 R))
    (hlogbound : ∀ J ∈ ball 0 R, ‖W J‖ ≤ A)
    {r : ℕ} (hr : 0 < r) (h : Fin r → E) :
    ‖iteratedFDeriv ℂ r (normalizedPartition W) 0 h‖ ≤
      Real.exp 1 * (2 * Real.exp 1 * (1 + A) / R) ^ r *
        r.factorial * ∏ j, ‖h j‖ := by
  have hsmall : R / (2 * (1 + A)) ≤ R := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + A))).mpr
    nlinarith
  have hδ : 0 < R / (2 * (1 + A)) := by positivity
  have hn := norm_iteratedFDeriv_le_cauchy_open hδ (Real.exp_pos 1).le
    ((normalizedPartition_analytic hanalytic).mono (ball_subset_ball hsmall))
    (normalizedPartition_polynomial_radius_bound hR hA hanalytic hlogbound) hr
  have hb := hn.trans (cauchy_to_factorial hδ (Real.exp_pos 1).le r)
  rw [div_div_eq_mul_div] at hb
  convert ContinuousMultilinearMap.le_of_opNorm_le hb h using 1
  ring

end YMUIC.OSGrowth
