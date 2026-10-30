import YM.OSGrowth.PolynomialMomentGrowth

set_option autoImplicit false
namespace YMUIC.OSTensor
open Metric Set OSGrowth

/-- Preserve the maximum shell in the polynomial local moment bound. -/
theorem max_shell_moment
    {r d : ℕ} (hr : 0 < r) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ρ A : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    (W : V → ℂ) (h : Fin r → V) (n : Fin r → ℕ)
    (hanalytic : AnalyticOnNhd ℂ W (ball 0 ρ))
    (hlog : ∀ J ∈ ball 0 ρ, ‖W J‖ ≤ A * (2 : ℝ) ^ (d * Finset.univ.sup n)) :
    ‖iteratedFDeriv ℂ r (normalizedPartition W) 0 h‖ ≤
      (Real.exp 1 * (2 * Real.exp 1 * (1 + A) / ρ) ^ r * r.factorial) *
        (2 : ℝ) ^ (d * r * Finset.univ.sup n) * ∏ j, ‖h j‖ := by
  let t : ℝ := 2 ^ (d * Finset.univ.sup n)
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num)
  have hb : 2 * Real.exp 1 * (1 + A * t) / ρ ≤
      (2 * Real.exp 1 * (1 + A) / ρ) * t := by
    calc
      _ ≤ 2 * Real.exp 1 * ((1 + A) * t) / ρ :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by nlinarith : 1 + A * t ≤ (1 + A) * t)
            (by positivity)) hρ.le
      _ = _ := by ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.exp 1 * (1 + A * t) / ρ) hb r
  have htPow : t ^ r = (2 : ℝ) ^ (d * r * Finset.univ.sup n) := by
    dsimp [t]
    rw [← pow_mul]
    congr 1
    ring
  rw [mul_pow, htPow] at hp
  have hm := local_moment_polynomial_growth hρ
    (show 0 ≤ A * t by positivity) hanalytic hlog hr h
  apply hm.trans
  calc
    _ ≤ Real.exp 1 * ((2 * Real.exp 1 * (1 + A) / ρ) ^ r *
        (2 : ℝ) ^ (d * r * Finset.univ.sup n)) * r.factorial * ∏ j, ‖h j‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (Real.exp_pos 1).le) (by positivity))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := by ring

end YMUIC.OSTensor
