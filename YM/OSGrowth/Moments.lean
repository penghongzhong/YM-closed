import YM.OSGrowth.Cauchy
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Metric Set

namespace YMUIC.OSGrowth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def normalizedPartition (W : E → ℂ) (J : E) : ℂ :=
  Complex.exp (W J - W 0)

theorem normalizedPartition_analytic {W : E → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ W (ball 0 R)) :
    AnalyticOnNhd ℂ (normalizedPartition W) (ball 0 R) :=
  (hf.sub analyticOnNhd_const).cexp

theorem normalizedPartition_half_radius_bound {W : E → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ W (ball 0 R))
    (hb : ∀ J ∈ ball 0 R, ‖W J‖ ≤ A) :
    ∀ J ∈ ball 0 (R / 2), ‖normalizedPartition W J‖ ≤ Real.exp A := by
  have hb0 := hb 0 (mem_ball_self hR)
  have hm : MapsTo W (ball 0 R) (closedBall (W 0) (2 * A)) := by
    intro J hJ
    simp only [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb J hJ])
  intro J hJ
  have hJR : J ∈ ball (0 : E) R := ball_subset_ball (by linarith) hJ
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf.differentiableOn hm hJR
  simp only [dist_eq_norm, sub_zero] at h
  have hn : ‖J‖ ≤ R / 2 := (mem_ball_zero_iff.mp hJ).le
  have hdiff : ‖W J - W 0‖ ≤ A := calc
    _ ≤ 2 * A / R * ‖J‖ := h
    _ ≤ 2 * A / R * (R / 2) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = A := by field_simp
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hdiff)

theorem local_moment_factorial_growth {W : E → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hanalytic : AnalyticOnNhd ℂ W (ball 0 R))
    (hlogbound : ∀ J ∈ ball 0 R, ‖W J‖ ≤ A)
    {r : ℕ} (hr : 0 < r) (h : Fin r → E) :
    ‖iteratedFDeriv ℂ r (normalizedPartition W) 0 h‖ ≤
      Real.exp A * (2 * (Real.exp 1 / R)) ^ r * r.factorial * ∏ j, ‖h j‖ := by
  have hn := norm_iteratedFDeriv_le_cauchy_open (half_pos hR) (Real.exp_pos A).le
    ((normalizedPartition_analytic hanalytic).mono (ball_subset_ball (by linarith)))
    (normalizedPartition_half_radius_bound hR hA hanalytic hlogbound) hr
  have hb := hn.trans (cauchy_to_factorial (half_pos hR) (Real.exp_pos A).le r)
  convert ContinuousMultilinearMap.le_of_opNorm_le hb h using 1
  ring

end YMUIC.OSGrowth
