import YM.OSTensor.SchwartzMixedElliptic
import YM.OSTensor.JointSchwartzControl

set_option autoImplicit false
namespace YMUIC.OSTensor

/-- Actual mixed fourth-order derivatives are controlled by the existing joint
Schwartz seminorm, both near the origin and at large distance. -/
theorem schwartz_mixed_joint_control (r q : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (4 * r))) ℂ)
    (v : List (EuclideanSpace ℝ (Fin (4 * r)))) (hv : ∀ a ∈ v, ‖a‖ ≤ 1)
    (x : EuclideanSpace ℝ (Fin (4 * r))) :
    (1 + ‖x‖ ^ q) * ‖schwartzMixedElliptic v f x‖ ≤
      (4 : ℝ) ^ v.length * jointSchwartzControl r q (4 * v.length) f := by
  have h0 := schwartz_mixed_elliptic_seminorm f v hv 0 0
  have hq := schwartz_mixed_elliptic_seminorm f v hv q 0
  have b0 := (schwartzMixedElliptic v f).norm_le_seminorm ℂ x
  have bq := (schwartzMixedElliptic v f).norm_pow_mul_le_seminorm ℂ q x
  have he : jointSchwartzControl r q (4 * v.length) f =
      (∑ j ∈ Finset.range (4 * v.length + 1), SchwartzMap.seminorm ℂ 0 j f) +
      ∑ j ∈ Finset.range (4 * v.length + 1), SchwartzMap.seminorm ℂ q j f := by
    simp [jointSchwartzControl, Finset.sum_add_distrib]
  rw [he, mul_add]
  simp only [zero_add] at h0 hq
  nlinarith
end YMUIC.OSTensor
