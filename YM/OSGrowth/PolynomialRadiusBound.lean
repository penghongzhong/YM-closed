import YM.OSGrowth.Moments

open Metric Set

namespace YMUIC.OSGrowth

/-- Shrinking the source radius by `1 + A` makes the normalized partition
function uniformly bounded by `exp 1`, without any additional hypothesis. -/
theorem normalizedPartition_polynomial_radius_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : E → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ W (ball 0 R))
    (hb : ∀ J ∈ ball 0 R, ‖W J‖ ≤ A) :
    ∀ J ∈ ball 0 (R / (2 * (1 + A))),
      ‖normalizedPartition W J‖ ≤ Real.exp 1 := by
  have hA1 : 0 < 1 + A := by positivity
  have hb0 := hb 0 (mem_ball_self hR)
  have hm : MapsTo W (ball 0 R) (closedBall (W 0) (2 * A)) := by
    intro J hJ
    simp only [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb J hJ])
  have hsmall : R / (2 * (1 + A)) ≤ R := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + A))).mpr
    nlinarith
  intro J hJ
  have hJR : J ∈ ball (0 : E) R := ball_subset_ball hsmall hJ
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf.differentiableOn hm hJR
  simp only [dist_eq_norm, sub_zero] at h
  have hn : ‖J‖ ≤ R / (2 * (1 + A)) := (mem_ball_zero_iff.mp hJ).le
  have hdiff : ‖W J - W 0‖ ≤ 1 := calc
    _ ≤ 2 * A / R * ‖J‖ := h
    _ ≤ 2 * A / R * (R / (2 * (1 + A))) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = A / (1 + A) := by field_simp
    _ ≤ 1 := (div_le_iff₀ hA1).mpr (by linarith)
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hdiff)

end YMUIC.OSGrowth
