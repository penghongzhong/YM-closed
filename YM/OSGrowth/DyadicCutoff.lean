import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import YM.OSGrowth.Cauchy

namespace YMUIC.OSGrowth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inner radius `2^n`, outer radius `2^(n+1)`, centered at zero. -/
def dyadicCutoff (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (2 : ℝ) ^ n
  rOut := (2 : ℝ) ^ (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

/-- A telescoping smooth partition: the initial ball and successive annuli. -/
noncomputable def dyadicShell [HasContDiffBump E] : ℕ → E → ℝ
  | 0 => dyadicCutoff (E := E) 0
  | n + 1 => fun x => dyadicCutoff (E := E) (n + 1) x - dyadicCutoff (E := E) n x

end YMUIC.OSGrowth
