import YM.OSGrowth.DyadicCutoff

open Metric

namespace YMUIC.OSGrowth

/-- The noninitial shell vanishes on the inner closed ball and outside the
outer open ball. These are actual support statements for the constructed bump. -/
theorem dyadic_shell_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    (n : ℕ) (x : E) :
    (‖x‖ ≤ (2 : ℝ) ^ n → dyadicShell (n + 1) x = 0) ∧
    ((2 : ℝ) ^ (n + 2) ≤ ‖x‖ → dyadicShell (n + 1) x = 0) := by
  have hstep : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  constructor
  · intro hx
    have ha : dyadicCutoff (E := E) n x = 1 :=
      (dyadicCutoff (E := E) n).one_of_mem_closedBall (by simpa [dyadicCutoff, dist_eq_norm] using hx)
    have hb : dyadicCutoff (E := E) (n + 1) x = 1 :=
      (dyadicCutoff (E := E) (n + 1)).one_of_mem_closedBall
        (by simpa [dyadicCutoff, dist_eq_norm] using hx.trans hstep)
    simp [dyadicShell, ha, hb]
  · intro hx
    have hstep' : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have ha : dyadicCutoff (E := E) n x = 0 :=
      (dyadicCutoff (E := E) n).zero_of_le_dist
        (by simpa [dyadicCutoff, dist_eq_norm] using hstep'.trans hx)
    have hb : dyadicCutoff (E := E) (n + 1) x = 0 :=
      (dyadicCutoff (E := E) (n + 1)).zero_of_le_dist
        (by simpa [dyadicCutoff, dist_eq_norm, Nat.add_assoc] using hx)
    simp [dyadicShell, ha, hb]

end YMUIC.OSGrowth
