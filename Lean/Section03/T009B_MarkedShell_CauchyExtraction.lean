import Mathlib

set_option autoImplicit false

/-!
# U2 marked-shell theorem: Cauchy extraction layer

The bidisc Cauchy theorem supplies the analytic input.  This file certifies
the exact scalar arithmetic converting that input and the shell supremum
bound into the covariance estimate.
-/

namespace YMUICV128.Section03.T009B

theorem cauchy_mixed_derivative_arithmetic
    (r C alpha weight derivNorm : ℝ)
    (hr : 0 < r)
    (hC : 0 ≤ C)
    (halpha : 0 ≤ alpha)
    (hweight : 0 ≤ weight)
    (hCauchy :
      derivNorm ≤ r⁻¹ * (r⁻¹ * (C * alpha * weight))) :
    derivNorm ≤ r⁻² * C * alpha * weight := by
  calc
    derivNorm
        ≤ r⁻¹ * (r⁻¹ * (C * alpha * weight)) := hCauchy
    _ = r⁻² * C * alpha * weight := by
      field_simp [ne_of_gt hr]
      <;> ring

theorem cauchy_mixed_derivative_exp
    (r C alpha mu d derivNorm : ℝ)
    (hr : 0 < r)
    (hC : 0 ≤ C)
    (halpha : 0 ≤ alpha)
    (hCauchy :
      derivNorm ≤
        r⁻¹ * (r⁻¹ *
          (C * alpha * Real.exp (-mu*d)))) :
    derivNorm ≤
      r⁻² * C * alpha * Real.exp (-mu*d) := by
  exact cauchy_mixed_derivative_arithmetic
    r C alpha (Real.exp (-mu*d)) derivNorm
    hr hC halpha (Real.exp_pos _).le hCauchy

theorem shell_bound_to_covariance_bound
    (r C alpha mu d covNorm shellSup : ℝ)
    (hr : 0 < r)
    (hC : 0 ≤ C)
    (halpha : 0 ≤ alpha)
    (hshell : shellSup ≤ C * alpha * Real.exp (-mu*d))
    (hcauchy : covNorm ≤ r⁻² * shellSup) :
    covNorm ≤ r⁻² * C * alpha * Real.exp (-mu*d) := by
  have hr2 : 0 ≤ r⁻² := by positivity
  calc
    covNorm ≤ r⁻² * shellSup := hcauchy
    _ ≤ r⁻² * (C * alpha * Real.exp (-mu*d)) :=
      mul_le_mul_of_nonneg_left hshell hr2
    _ = r⁻² * C * alpha * Real.exp (-mu*d) := by ring

#print axioms cauchy_mixed_derivative_arithmetic
#print axioms cauchy_mixed_derivative_exp
#print axioms shell_bound_to_covariance_bound

end YMUICV128.Section03.T009B
