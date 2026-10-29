import Mathlib.Analysis.PSeries

set_option autoImplicit false
namespace YMUIC.OSTensor

/-- The residual quadratic weight after applying two source derivatives is
summable over the actual integer Fourier lattice. -/
theorem fourier_quadratic_weight :
    Summable (fun k : ℤ => 1 / (1 + |(k : ℝ)|) ^ 2) := by
  have hn : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hn
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hn

end YMUIC.OSTensor
