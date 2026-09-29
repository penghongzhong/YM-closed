import Mathlib

set_option autoImplicit false

/-! Finite stationary-flux energy estimate. This is not a global spectral-gap assertion. -/
namespace YMUICV128.Repair.T013A

theorem two_point_square {E : Type*} [SeminormedAddCommGroup E]
    (x y c : E) : ‖y - x‖ ^ 2 ≤ 2 * ‖y - c‖ ^ 2 + 2 * ‖x - c‖ ^ 2 := by
  have ht : ‖y - x‖ ≤ ‖y - c‖ + ‖x - c‖ := by
    calc
      ‖y - x‖ ≤ ‖y - c‖ + ‖c - x‖ := norm_sub_le _ _ _
      _ = _ := by rw [norm_sub_rev c x]
  have hs := mul_self_le_mul_self (norm_nonneg (y - x)) ht
  nlinarith [sq_nonneg (‖y - c‖ - ‖x - c‖)]

theorem finite_stationary_flux_energy {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E]
    (p : ι → ℝ) (w : ι → ι → ℝ) (f : ι → E) (c : E)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, (∑ j, w i j) ≤ p i)
    (hcol : ∀ j, (∑ i, w i j) ≤ p j) :
    (∑ i, ∑ j, w i j * ‖f j - f i‖ ^ 2) ≤
      4 * ∑ i, p i * ‖f i - c‖ ^ 2 := by
  let a : ι → ℝ := fun i => ‖f i - c‖ ^ 2
  have ha (i : ι) : 0 ≤ a i := sq_nonneg _
  have hy : (∑ i, ∑ j, w i j * (2 * a j)) ≤ 2 * ∑ j, p j * a j := by
    calc
      (∑ i, ∑ j, w i j * (2 * a j)) = ∑ j, ∑ i, w i j * (2 * a j) := Finset.sum_comm
      _ = ∑ j, (∑ i, w i j) * (2 * a j) := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ j, p j * (2 * a j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hcol j) (by positivity)
      _ = 2 * ∑ j, p j * a j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hx : (∑ i, ∑ j, w i j * (2 * a i)) ≤ 2 * ∑ i, p i * a i := by
    calc
      (∑ i, ∑ j, w i j * (2 * a i)) = ∑ i, (∑ j, w i j) * (2 * a i) := by
        simp_rw [Finset.sum_mul]
      _ ≤ ∑ i, p i * (2 * a i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hrow i) (by positivity)
      _ = 2 * ∑ i, p i * a i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    (∑ i, ∑ j, w i j * ‖f j - f i‖ ^ 2) ≤
        ∑ i, ∑ j, w i j * (2 * a j + 2 * a i) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (two_point_square (f i) (f j) c) (hw i j)
    _ = (∑ i, ∑ j, w i j * (2 * a j)) + (∑ i, ∑ j, w i j * (2 * a i)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ (2 * ∑ i, p i * a i) + (2 * ∑ i, p i * a i) := add_le_add hy hx
    _ = _ := by dsimp [a]; ring

theorem metropolis_flux_symmetric {ι : Type*}
    (p : ι → ℝ) (q : ι → ι → ℝ) (hq : ∀ i j, q i j = q j i) (i j : ι) :
    q i j * min (p i) (p j) = q j i * min (p j) (p i) := by
  rw [hq i j, min_comm]

theorem metropolis_flux_row_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (q : ι → ι → ℝ)
    (hq0 : ∀ i j, 0 ≤ q i j) (hq1 : ∀ i, ∑ j, q i j = 1) (i : ι) :
    (∑ j, q i j * min (p i) (p j)) ≤ p i := by
  calc
    (∑ j, q i j * min (p i) (p j)) ≤ ∑ j, q i j * p i := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hq0 i j)
    _ = p i := by rw [← Finset.sum_mul, hq1 i]; ring

#print axioms two_point_square
#print axioms finite_stationary_flux_energy
#print axioms metropolis_flux_symmetric
#print axioms metropolis_flux_row_bound
end YMUICV128.Repair.T013A
