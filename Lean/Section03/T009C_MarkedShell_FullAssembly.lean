import Mathlib

set_option autoImplicit false

/-!
# U2 marked-shell theorem: final bound assembly

This file certifies the final implication after the paper-specific source
identification has supplied the mixed derivative norm and the three-channel
shell supremum.  No Yang--Mills-specific analytic estimate is postulated here.
-/

namespace YMUICV128.Section03.T009C

theorem marked_shell_covariance_final
    (r C A g e mu d covNorm shellSup : ℝ)
    (hr : 0 < r)
    (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hg : 0 ≤ g) (he : 0 ≤ e)
    (hshell :
      shellSup ≤ C * (A + g + e) * Real.exp (-mu*d))
    (hcauchy :
      covNorm ≤ r⁻² * shellSup) :
    covNorm ≤
      (r⁻² * C) * (A + g + e) * Real.exp (-mu*d) := by
  have hr2 : 0 ≤ r⁻² := by positivity
  calc
    covNorm
        ≤ r⁻² * shellSup := hcauchy
    _ ≤ r⁻² * (C * (A + g + e) * Real.exp (-mu*d)) :=
      mul_le_mul_of_nonneg_left hshell hr2
    _ = (r⁻² * C) * (A + g + e) * Real.exp (-mu*d) := by
      ring

theorem marked_shell_covariance_with_named_activity
    (r C alpha mu d covNorm shellSup : ℝ)
    (hr : 0 < r)
    (hC : 0 ≤ C)
    (halpha : 0 ≤ alpha)
    (hshell :
      shellSup ≤ C * alpha * Real.exp (-mu*d))
    (hcauchy :
      covNorm ≤ r⁻² * shellSup) :
    covNorm ≤
      (r⁻² * C) * alpha * Real.exp (-mu*d) := by
  have hr2 : 0 ≤ r⁻² := by positivity
  calc
    covNorm
        ≤ r⁻² * shellSup := hcauchy
    _ ≤ r⁻² * (C * alpha * Real.exp (-mu*d)) :=
      mul_le_mul_of_nonneg_left hshell hr2
    _ = (r⁻² * C) * alpha * Real.exp (-mu*d) := by
      ring

#print axioms marked_shell_covariance_final
#print axioms marked_shell_covariance_with_named_activity

end YMUICV128.Section03.T009C
