import Mathlib

set_option autoImplicit false

namespace YMUICV128.Repair.T013D

noncomputable def delta (r q q4 : ℝ) : ℝ :=
  (64 / 9 : ℝ) * q * r ^ 2 - (32 / 9 : ℝ) * r ^ 3 * (q ^ 2 + q4)

theorem quartic_coordinate_budget (a b c : ℝ) :
    a ^ 4 + b ^ 4 + c ^ 4 ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg b),
    mul_nonneg (sq_nonneg a) (sq_nonneg c), mul_nonneg (sq_nonneg b) (sq_nonneg c)]

theorem delta_exact_certificate (r q q4 : ℝ) :
    delta r q q4 - (16 / 3 : ℝ) * q * r ^ 2 =
      (16 / 9 : ℝ) * q * r ^ 2 * (1 - 4 * r * q) +
        (32 / 9 : ℝ) * r ^ 3 * (q ^ 2 - q4) := by
  unfold delta
  ring

theorem noncentral_curvature_lower (r q q4 : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq4 : q4 ≤ q ^ 2) :
    (16 / 3 : ℝ) * q * r ^ 2 ≤ delta r q q4 := by
  have hprod := mul_le_mul_of_nonneg_left hq1 hr0
  have hrem : 0 ≤ 1 - 4 * r * q := by nlinarith
  have h1 : 0 ≤ (16 / 9 : ℝ) * q * r ^ 2 * (1 - 4 * r * q) := by positivity
  have h2 : 0 ≤ (32 / 9 : ℝ) * r ^ 3 * (q ^ 2 - q4) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hq4)
  have he := delta_exact_certificate r q q4
  linarith

/-- Applies to every coefficient combination, not merely to coordinate-axis tests. -/
theorem coherent_weighted_lower {ι : Type*} [Fintype ι]
    (p q q4 v : ι → ℝ) (r : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hq4 : ∀ i, q4 i ≤ q i ^ 2) :
    (16 / 3 : ℝ) * r ^ 2 * (∑ i, p i * q i * v i ^ 2) ≤
      ∑ i, p i * delta r (q i) (q4 i) * v i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left
    (noncentral_curvature_lower r (q i) (q4 i) hr0 hr1 (hq0 i) (hq1 i) (hq4 i))
    (mul_nonneg (hp i) (sq_nonneg (v i)))
  nlinarith only [h]

#print axioms quartic_coordinate_budget
#print axioms delta_exact_certificate
#print axioms noncentral_curvature_lower
#print axioms coherent_weighted_lower
end YMUICV128.Repair.T013D
