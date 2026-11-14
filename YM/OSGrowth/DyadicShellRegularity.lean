import YM.OSGrowth.DyadicCutoff

open scoped ContDiff

namespace YMUIC.OSGrowth

/-- Each shell is smooth and compactly supported, with absolute value at most
one. Finite-dimensionality supplies compactness, not an external interface. -/
theorem dyadic_shell_regularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E] (n : ℕ) :
    ContDiff ℝ ∞ (dyadicShell n : E → ℝ) ∧
    HasCompactSupport (dyadicShell n : E → ℝ) ∧
    ∀ x : E, ‖dyadicShell n x‖ ≤ 1 := by
  cases n with
  | zero =>
    refine ⟨(dyadicCutoff (E := E) 0).contDiff, (dyadicCutoff (E := E) 0).hasCompactSupport, ?_⟩
    intro x
    simpa [dyadicShell, Real.norm_eq_abs, abs_of_nonneg (dyadicCutoff (E := E) 0).nonneg]
      using (dyadicCutoff (E := E) 0).le_one (x := x)
  | succ n =>
    refine ⟨(dyadicCutoff (E := E) (n + 1)).contDiff.sub (dyadicCutoff (E := E) n).contDiff,
      (dyadicCutoff (E := E) (n + 1)).hasCompactSupport.sub (dyadicCutoff (E := E) n).hasCompactSupport, ?_⟩
    intro x
    change ‖dyadicCutoff (E := E) (n + 1) x - dyadicCutoff (E := E) n x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_le]
    have h0 := (dyadicCutoff (E := E) n).nonneg (x := x)
    have h1 := (dyadicCutoff (E := E) n).le_one (x := x)
    have h2 := (dyadicCutoff (E := E) (n + 1)).nonneg (x := x)
    have h3 := (dyadicCutoff (E := E) (n + 1)).le_one (x := x)
    constructor <;> linarith

end YMUIC.OSGrowth
