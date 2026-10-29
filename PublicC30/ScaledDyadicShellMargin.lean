import YM.OSGrowth.DyadicShellAnnulus

set_option autoImplicit false

namespace YMUIC.OSTensor
open YMUIC.OSGrowth

/--
The *actual* dyadic shell is supported in a strict annulus after
normalizing its physical scale by 2^(n+4). The two margins are uniform in n,
and provide a boundary-free radial patch for subsequent torus periodization.
They do NOT claim the actual periodic extension has been constructed.
-/
theorem scaled_dyadic_shell_outer_margin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (n : ℕ) (y : E)
    (hy : (1 / 4 : ℝ) ≤ ‖y‖) :
    dyadicShell (E := E) (n + 1) ((2 : ℝ) ^ (n + 4) • y) = 0 := by
  apply (dyadic_shell_annulus (E := E) n ((2 : ℝ) ^ (n + 4) • y)).2
  change (2 : ℝ) ^ (n + 2) ≤ ‖(2 : ℝ) ^ (n + 4) • y‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : (2 : ℝ) ^ (n + 4) = 4 * (2 : ℝ) ^ (n + 2) := by
    rw [show n + 4 = (n + 2) + 2 by omega, pow_add]
    norm_num
    ring
  rw [hp]
  have hm : (2 : ℝ) ^ (n + 2) * (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (n + 2) * ‖y‖ :=
    mul_le_mul_of_nonneg_left hy (by positivity)
  nlinarith

theorem scaled_dyadic_shell_inner_margin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (n : ℕ) (y : E)
    (hy : ‖y‖ ≤ (1 / 16 : ℝ)) :
    dyadicShell (E := E) (n + 1) ((2 : ℝ) ^ (n + 4) • y) = 0 := by
  apply (dyadic_shell_annulus (E := E) n ((2 : ℝ) ^ (n + 4) • y)).1
  change ‖(2 : ℝ) ^ (n + 4) • y‖ ≤ (2 : ℝ) ^ n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : (2 : ℝ) ^ (n + 4) = 16 * (2 : ℝ) ^ n := by
    rw [pow_add]
    norm_num
    ring
  rw [hp]
  have hm : (2 : ℝ) ^ n * ‖y‖ ≤
      (2 : ℝ) ^ n * (1 / 16 : ℝ) :=
    mul_le_mul_of_nonneg_left hy (by positivity)
  nlinarith

end YMUIC.OSTensor
