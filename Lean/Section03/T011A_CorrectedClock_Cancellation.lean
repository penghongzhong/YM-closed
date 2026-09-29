import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T011A

theorem corrected_clock_linear_cancellation (Gamma C x rho : ℝ)
    (hG : Gamma ≠ 0) (hx : x ≠ 0) :
    (1 / Gamma - C / (Gamma ^ 2 * x)) * (-Gamma - C / x + rho) =
      -1 + rho / Gamma + C ^ 2 / (Gamma ^ 2 * x ^ 2) - C * rho / (Gamma ^ 2 * x) := by
  field_simp [hG, hx]
  ring

theorem corrected_clock_error_triangle (Gamma C x rho quad : ℝ)
    (hG : 0 < Gamma) (hx : 0 < x) (hquad : |quad| ≤ x⁻¹ * x⁻¹)
    (hlin : |rho / Gamma + C ^ 2 / (Gamma ^ 2 * x ^ 2) - C * rho / (Gamma ^ 2 * x)| ≤
      |rho| / Gamma + (C ^ 2 / Gamma ^ 2) * (x⁻¹ * x⁻¹) +
        (|C| / Gamma ^ 2) * |rho| * x⁻¹) :
    |rho / Gamma + C ^ 2 / (Gamma ^ 2 * x ^ 2) - C * rho / (Gamma ^ 2 * x) + quad| ≤
      |rho| / Gamma + (C ^ 2 / Gamma ^ 2) * (x⁻¹ * x⁻¹) +
        (|C| / Gamma ^ 2) * |rho| * x⁻¹ + x⁻¹ * x⁻¹ := by
  have ht :
      |rho / Gamma + C ^ 2 / (Gamma ^ 2 * x ^ 2) - C * rho / (Gamma ^ 2 * x) + quad| ≤
      |rho / Gamma + C ^ 2 / (Gamma ^ 2 * x ^ 2) - C * rho / (Gamma ^ 2 * x)| + |quad| := by
    simpa only [Real.norm_eq_abs] using norm_add_le
      (rho / Gamma + C ^ 2 / (Gamma ^ 2 * x ^ 2) - C * rho / (Gamma ^ 2 * x)) quad
  exact ht.trans (add_le_add hlin hquad)

#print axioms corrected_clock_linear_cancellation
#print axioms corrected_clock_error_triangle

end YMUICV128.Section03.T011A
