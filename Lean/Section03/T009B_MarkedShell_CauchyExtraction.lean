import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T009B

theorem cauchy_mixed_derivative_arithmetic
    (r C alpha weight derivNorm : ℝ)
    (hr : 0 < r)
    (hCauchy :
      derivNorm ≤ r⁻¹ * (r⁻¹ * (C * alpha * weight))) :
    derivNorm ≤ (r⁻¹ * r⁻¹) * C * alpha * weight := by
  calc
    derivNorm ≤ r⁻¹ * (r⁻¹ * (C * alpha * weight)) := hCauchy
    _ = (r⁻¹ * r⁻¹) * C * alpha * weight := by ring

theorem shell_bound_to_covariance_bound
    (r C alpha mu d covNorm shellSup : ℝ)
    (hshell : shellSup ≤ C * alpha * Real.exp (-mu*d))
    (hcauchy : covNorm ≤ (r⁻¹ * r⁻¹) * shellSup)
    (hr2 : 0 ≤ r⁻¹ * r⁻¹) :
    covNorm ≤ (r⁻¹ * r⁻¹) * C * alpha * Real.exp (-mu*d) := by
  calc
    covNorm ≤ (r⁻¹ * r⁻¹) * shellSup := hcauchy
    _ ≤ (r⁻¹ * r⁻¹) * (C * alpha * Real.exp (-mu*d)) :=
      mul_le_mul_of_nonneg_left hshell hr2
    _ = (r⁻¹ * r⁻¹) * C * alpha * Real.exp (-mu*d) := by ring

#print axioms cauchy_mixed_derivative_arithmetic
#print axioms shell_bound_to_covariance_bound

end YMUICV128.Section03.T009B
