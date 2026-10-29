import YM.OSGrowth.DyadicShellDerivativeBound

set_option autoImplicit false
namespace YMUIC.OSGrowth

/-- After scaling a genuine shell by its physical dyadic radius, the
m-th directional/Frechet derivative is bounded independently of the shell
index n.  No derivative majorant is a hypothesis. -/
theorem scaled_dyadic_shell_uniform_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    (n m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m
      (fun y : E => dyadicShell (E := E) (n + 1) ((2 : ℝ) ^ (n + 4) • y)) x‖ ≤
      2 * (2 : ℝ) ^ (4 * m) *
        SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E)) := by
  have hs : ContDiff ℝ m (dyadicShell (E := E) (n + 1)) :=
    ((dyadic_shell_regularity (E := E) (n + 1)).1).of_le (by simp)
  rw [iteratedFDeriv_comp_const_smul ((2 : ℝ) ^ (n + 4)) hs]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  let M : ℝ := SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E))
  have hbound := dyadic_shell_all_derivatives_bound (E := E) n m
    ((2 : ℝ) ^ (n + 4) • x)
  have hpow : ((2 : ℝ) ^ (n + 4)) ^ m =
      (2 : ℝ) ^ (n * m) * (2 : ℝ) ^ (4 * m) := by
    rw [← pow_mul, show (n + 4) * m = n * m + 4 * m by ring, pow_add]
  calc
    ((2 : ℝ) ^ (n + 4)) ^ m *
        ‖iteratedFDeriv ℝ m (dyadicShell (E := E) (n + 1))
          ((2 : ℝ) ^ (n + 4) • x)‖ ≤
      ((2 : ℝ) ^ (n + 4)) ^ m * (2 * M / (2 : ℝ) ^ (n * m)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * (2 : ℝ) ^ (4 * m) * M := by
      rw [hpow]
      have hp : (2 : ℝ) ^ (n * m) ≠ 0 := by positivity
      field_simp [hp]
      ring

end YMUIC.OSGrowth
