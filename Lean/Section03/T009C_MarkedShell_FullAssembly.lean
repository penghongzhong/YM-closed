import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T009C

theorem marked_shell_covariance_final
    (r C A g e mu d covNorm shellSup : ℝ)
    (hr : 0 < r)
    (hshell :
      shellSup ≤ C * (A + g + e) * Real.exp (-mu*d))
    (hcauchy :
      covNorm ≤ (r⁻¹ * r⁻¹) * shellSup) :
    covNorm ≤
      ((r⁻¹ * r⁻¹) * C) * (A + g + e) * Real.exp (-mu*d) := by
  have hr2 : 0 ≤ r⁻¹ * r⁻¹ := mul_nonneg (inv_nonneg.mpr hr.le) (inv_nonneg.mpr hr.le)
  calc
    covNorm ≤ (r⁻¹ * r⁻¹) * shellSup := hcauchy
    _ ≤ (r⁻¹ * r⁻¹) * (C * (A + g + e) * Real.exp (-mu*d)) :=
      mul_le_mul_of_nonneg_left hshell hr2
    _ = ((r⁻¹ * r⁻¹) * C) * (A + g + e) * Real.exp (-mu*d) := by ring

#print axioms marked_shell_covariance_final

end YMUICV128.Section03.T009C
