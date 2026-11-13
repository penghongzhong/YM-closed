import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-- Exact factorial cancellation for one distinguished marked root.
This is the algebraic coefficient identity behind the fixed-q slot:
(n+1)/(n+1)! = 1/n!. -/
theorem original24_one_marked_factorial_exact (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * ((Nat.factorial (n + 1) : ℝ)⁻¹) =
      (Nat.factorial n : ℝ)⁻¹ := by
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf]

/-- The same exact cancellation after multiplying by an arbitrary
bulk/source/tree weight. This is the coefficient form used by the
one-marked-root extraction in the FP series. -/
theorem original24_one_marked_weight_exact
    (n : ℕ) (w : ℝ) :
    (((n + 1 : ℕ) : ℝ) * w) / (Nat.factorial (n + 1) : ℝ) =
      w / (Nat.factorial n : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf]

end YMUIC.Original24
