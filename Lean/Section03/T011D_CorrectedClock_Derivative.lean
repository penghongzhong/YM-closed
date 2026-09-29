import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T011D

noncomputable def correctedClock (Gamma C x : ℝ) : ℝ :=
  x / Gamma - (C / Gamma ^ 2) * Real.log x

theorem correctedClock_hasDerivAt (Gamma C x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (correctedClock Gamma C)
      (1 / Gamma - C / (Gamma ^ 2 * x)) x := by
  have h := ((hasDerivAt_id x).div_const Gamma).sub
    ((Real.hasDerivAt_log hx).const_mul (C / Gamma ^ 2))
  convert h using 1 <;> simp only [correctedClock, div_eq_mul_inv, mul_inv_rev] <;> ring

theorem correctedClock_deriv (Gamma C x : ℝ) (hx : x ≠ 0) :
    deriv (correctedClock Gamma C) x = 1 / Gamma - C / (Gamma ^ 2 * x) :=
  (correctedClock_hasDerivAt Gamma C x hx).deriv

theorem correctedClock_derivative_lower (Gamma C xw x : ℝ)
    (hG : 0 < Gamma) (hC : 0 ≤ C) (hxw : 0 < xw)
    (hwindow : 2 * C / Gamma < xw) (hx : xw ≤ x) :
    1 / (2 * Gamma) ≤ 1 / Gamma - C / (Gamma ^ 2 * x) := by
  have hx0 : 0 < x := lt_of_lt_of_le hxw hx
  have hCx : 2 * C < Gamma * x := by
    have hw := (div_lt_iff₀ hG).mp hwindow
    have hm := mul_le_mul_of_nonneg_left hx hG.le
    nlinarith
  have hterm : C / (Gamma ^ 2 * x) ≤ 1 / (2 * Gamma) := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hG) hx0) (mul_pos (by norm_num) hG)).2
    nlinarith [mul_lt_mul_of_pos_left hCx hG]
  have hid : 1 / Gamma = 1 / (2 * Gamma) + 1 / (2 * Gamma) := by ring
  linarith

theorem correctedClock_strictMonoOn (Gamma C xw : ℝ)
    (hG : 0 < Gamma) (hC : 0 ≤ C) (hxw : 0 < xw)
    (hwindow : 2 * C / Gamma < xw) :
    StrictMonoOn (correctedClock Gamma C) (Set.Ici xw) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici xw)
  · intro x hx
    exact (correctedClock_hasDerivAt Gamma C x
      (ne_of_gt (lt_of_lt_of_le hxw hx))).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : xw ≤ x := Set.interior_subset hx
    rw [correctedClock_deriv Gamma C x (ne_of_gt (lt_of_lt_of_le hxw hx'))]
    exact lt_of_lt_of_le (by positivity)
      (correctedClock_derivative_lower Gamma C xw x hG hC hxw hwindow hx')

#print axioms correctedClock_hasDerivAt
#print axioms correctedClock_deriv
#print axioms correctedClock_derivative_lower
#print axioms correctedClock_strictMonoOn

end YMUICV128.Section03.T011D
