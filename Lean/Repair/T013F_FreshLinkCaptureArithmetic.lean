import Mathlib

set_option autoImplicit false

/-! Arithmetic sublemmas for conditional fresh-link capture, not physical source payment. -/
namespace YMUICV128.Repair.T013F

theorem symmetric_rotation_square (a b : ℝ) :
    ((a + b) ^ 2 + (a - b) ^ 2) / 2 = a ^ 2 + b ^ 2 := by ring

theorem theta_rotation_average (r q : ℝ) :
    1 - ((1 - r) * (1 - q) + r * q / 3) = r + (1 - 4 * r / 3) * q := by ring

theorem theta_rotation_lower (r q : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) (hq : 0 ≤ q) :
    r ≤ r + (1 - 4 * r / 3) * q := by
  have h : 0 ≤ 1 - 4 * r / 3 := by linarith
  exact le_add_of_nonneg_right (mul_nonneg h hq)

theorem weighted_capture (kappa mass activity thetaMass : ℝ)
    (hcomparison : kappa * (mass - activity) ≤ 2 * thetaMass + 2 * activity) :
    kappa / 2 * mass - (1 + kappa / 2) * activity ≤ thetaMass := by
  nlinarith only [hcomparison]

theorem capture_threshold (kappa mass activity thetaMass : ℝ)
    (hk : 0 < kappa)
    (hcapture : kappa / 2 * mass - (1 + kappa / 2) * activity ≤ thetaMass)
    (hsmall : activity ≤ kappa / (2 * (kappa + 2)) * mass) :
    kappa / 4 * mass ≤ thetaMass := by
  have hp : 0 ≤ 1 + kappa / 2 := by linarith
  have hb := mul_le_mul_of_nonneg_left hsmall hp
  have hid : (1 + kappa / 2) * (kappa / (2 * (kappa + 2)) * mass) =
      kappa / 4 * mass := by
    field_simp [show kappa + 2 ≠ 0 by linarith]
    ring
  rw [hid] at hb
  linarith

theorem threshold_ge_sixth (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    kappa / 6 ≤ kappa / (2 * (kappa + 2)) := by
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hk1 hk0]

#print axioms symmetric_rotation_square
#print axioms theta_rotation_average
#print axioms theta_rotation_lower
#print axioms weighted_capture
#print axioms capture_threshold
#print axioms threshold_ge_sixth
end YMUICV128.Repair.T013F
