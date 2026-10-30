import YMOriginal.Original30_VolumeUniformWilsonSchwartz
import YMOriginal.Original30_JointLatticeSchwartz

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# Original30: simultaneous joint-test Schwartz decay in 4r dimensions

A joint Schwartz test on R^(4r) pays for the PRODUCT of r actual
four-dimensional site weights, with a constant growing exponentially
in r and with a Schwartz weight order EXACTLY 8r.

Unlike a pure-test tensor estimate, this applies to arbitrary
F in S(R^(4r)). It is a purely analytic lemma; the separate
physical model/renormalized source dictionary is not asserted.
-/

/-- Polynomial estimate with a constant exponential in the number
of field insertions, and independent of the magnitude of t. -/
theorem one_add_pow_uniform
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ r ≤ (2 : ℝ) ^ r * (1 + t ^ r) := by
  by_cases hsmall : t ≤ 1
  · have hle : 1 + t ≤ 2 := by linarith
    calc
      (1 + t) ^ r ≤ (2 : ℝ) ^ r :=
        pow_le_pow_left₀ (by positivity) hle r
      _ ≤ (2 : ℝ) ^ r * (1 + t ^ r) := by
        have htn : 0 ≤ t ^ r := pow_nonneg ht r
        have htwon : 0 ≤ (2 : ℝ) ^ r := by positivity
        nlinarith
  · have hle : 1 + t ≤ 2 * t := by linarith
    calc
      (1 + t) ^ r ≤ (2 * t) ^ r :=
        pow_le_pow_left₀ (by positivity) hle r
      _ = (2 : ℝ) ^ r * t ^ r := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ r * (1 + t ^ r) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- The actual 4r-dimensional Schwartz norm pays for r simultaneous
4D site weights with no spatial volume, cutoff, or r! loss.
The geometric compatibility below holds for the canonical joint
location (x_(p1),...,x_(pr)); its concrete coordinate proof is
tracked separately. -/
theorem joint_schwartz_pays_product_spatial_weights
    (r : ℕ)
    (sites : Fin r → Space4)
    (y : EuclideanSpace ℝ (Fin (4 * r)))
    (hgeom : ∀ j, ‖sites j‖ ≤ ‖y‖)
    (f : YMUIC.Original34.JointTest r) :
    (∏ j : Fin r, (1 + ‖sites j‖ ^ 8)) * ‖f y‖ ≤
      (2 : ℝ) ^ r *
      (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  have hp :
      (∏ j : Fin r, (1 + ‖sites j‖ ^ 8)) ≤
        (1 + ‖y‖ ^ 8) ^ r := by
    calc
      (∏ j : Fin r, (1 + ‖sites j‖ ^ 8)) ≤
        ∏ _j : Fin r, (1 + ‖y‖ ^ 8) := by
          apply Finset.prod_le_prod₀
          · intro j hj
            positivity
          · intro j hj
            have hjBound := pow_le_pow_left₀
              (norm_nonneg (sites j)) (hgeom j) 8
            linarith
      _ = (1 + ‖y‖ ^ 8) ^ r := by simp
  have hweight :
      (1 + ‖y‖ ^ (8 * r)) * ‖f y‖ ≤
        SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f := by
    have h0 := f.norm_le_seminorm ℂ y
    have hq := f.norm_pow_mul_le_seminorm ℂ (8 * r) y
    nlinarith
  calc
    (∏ j : Fin r, (1 + ‖sites j‖ ^ 8)) * ‖f y‖ ≤
      (1 + ‖y‖ ^ 8) ^ r * ‖f y‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ ≤ ((2 : ℝ) ^ r * (1 + (‖y‖ ^ 8) ^ r)) * ‖f y‖ :=
        mul_le_mul_of_nonneg_right
          (one_add_pow_uniform r (‖y‖ ^ 8) (pow_nonneg (norm_nonneg _) _))
          (norm_nonneg _)
    _ = (2 : ℝ) ^ r *
        ((1 + ‖y‖ ^ (8 * r)) * ‖f y‖) := by
          rw [pow_mul]
          ring
    _ ≤ (2 : ℝ) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)

end YMUIC.Original30
