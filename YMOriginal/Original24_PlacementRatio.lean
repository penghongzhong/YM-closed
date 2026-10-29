import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original24 4D placement entropy versus B10 fifth-order Taylor gain

The exact paper exponent is
  L^(4m) * L^(-(5-theta)m) = q^m,
  q = L^(-(1-theta)),  L>1, 0<theta<1.

Unlike earlier helper code, q<1 is here derived from the genuine
lattice dilation and Taylor exponent, not inserted as an unrelated
numerical hypothesis.
-/

theorem original24_four_dimensional_q_contracts
    (L theta : ℝ) (hL : 1 < L)
    (_htheta0 : 0 < theta) (htheta1 : theta < 1) :
    0 < L ^ (-(1 - theta) : ℝ) ∧
      L ^ (-(1 - theta) : ℝ) < 1 := by
  constructor
  · exact Real.rpow_pos_of_pos (by linarith) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

/-- The five derivative gain beats the four-dimensional placement factor
by exactly 1-theta, independently of the number of RG steps. -/
theorem original24_four_dimensional_power_identity
    (L theta : ℝ) (hL : 1 < L) (m : ℕ) :
    L ^ (4 * m) * L ^ (-(5 - theta) * (m : ℝ)) =
      (L ^ (-(1 - theta) : ℝ)) ^ m := by
  have hL0 : 0 ≤ L := by linarith
  calc
    L ^ (4 * m) * L ^ (-(5 - theta) * (m : ℝ)) =
        L ^ ((4 * m : ℕ) : ℝ) * L ^ (-(5 - theta) * (m : ℝ)) := by
          rw [Real.rpow_natCast]
    _ = L ^ (((4 * m : ℕ) : ℝ) + (-(5 - theta) * (m : ℝ))) := by
          rw [Real.rpow_add hL0]
    _ = L ^ (-(1 - theta) * (m : ℝ)) := by
          congr 1
          push_cast
          ring
    _ = (L ^ (-(1 - theta) : ℝ)) ^ m := by
          rw [Real.rpow_mul hL0, Real.rpow_natCast]

end YMUIC.Original24
