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

end YMUIC.Original24
