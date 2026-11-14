import YM.OSGrowth.DyadicCutoffDerivativeBound
import YM.OSGrowth.DyadicShellRegularity

set_option autoImplicit false
namespace YMUIC.OSGrowth

/-- The actual dyadic-shell derivative has a scale-uniform bound at every
order, obtained from the two genuine rescaled fixed cutoffs. This creates
the missing high-order derivative budget for periodization, without an
assumed derivative majorant. -/
theorem dyadic_shell_all_derivatives_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    (n m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (dyadicShell (E := E) (n + 1)) x‖ ≤
      (2 * SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E))) /
        (2 : ℝ) ^ (n * m) := by
  let M : ℝ := SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E))
  have hM : 0 ≤ M := apply_nonneg _ _
  have hp : (2 : ℝ) ^ (n * m) ≤ (2 : ℝ) ^ ((n + 1) * m) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.mul_le_mul_right m (Nat.le_succ n))
  have hdiv : M / (2 : ℝ) ^ ((n + 1) * m) ≤ M / (2 : ℝ) ^ (n * m) :=
    div_le_div_of_nonneg_left hM (by positivity) hp
  have hc1 : ContDiff ℝ m (dyadicCutoff (E := E) (n + 1)) :=
    (dyadicCutoff (E := E) (n + 1)).contDiff
  have hc0 : ContDiff ℝ m (dyadicCutoff (E := E) n) :=
    (dyadicCutoff (E := E) n).contDiff
  have hd :
      iteratedFDeriv ℝ m (dyadicShell (E := E) (n + 1)) x =
        iteratedFDeriv ℝ m (dyadicCutoff (E := E) (n + 1)) x -
          iteratedFDeriv ℝ m (dyadicCutoff (E := E) n) x := by
    have heq : (dyadicShell (E := E) (n + 1) : E → ℝ) =
        (dyadicCutoff (E := E) (n + 1) : E → ℝ) -
          (dyadicCutoff (E := E) n : E → ℝ) := by
      funext y
      rfl
    rw [heq]
    exact iteratedFDeriv_sub_apply hc1.contDiffAt hc0.contDiffAt
  rw [hd]
  have h1 := dyadic_cutoff_derivative_bound (E := E) (n + 1) m x
  have h0 := dyadic_cutoff_derivative_bound (E := E) n m x
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (dyadicCutoff (E := E) (n + 1)) x‖ +
          ‖iteratedFDeriv ℝ m (dyadicCutoff (E := E) n) x‖ := norm_sub_le _ _
    _ ≤ M / (2 : ℝ) ^ ((n + 1) * m) + M / (2 : ℝ) ^ (n * m) := by
      exact add_le_add h1 h0
    _ ≤ M / (2 : ℝ) ^ (n * m) + M / (2 : ℝ) ^ (n * m) :=
      add_le_add_left hdiv _
    _ = (2 * SchwartzMap.seminorm ℝ 0 m (baseCutoffSchwartz (E := E))) /
          (2 : ℝ) ^ (n * m) := by
      dsimp [M]
      ring

end YMUIC.OSGrowth
