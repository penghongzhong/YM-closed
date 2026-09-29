import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T011C

theorem finite_clock_error_bound
    (e : ℕ → ℝ) (b : ℕ → ℝ)
    (K n : ℕ)
    (hnK : n ≤ K)
    (he : ∀ j < K, |e j| ≤ b j)
    (hb0 : ∀ j < K, 0 ≤ b j)
    (hbudget : (Finset.range K).sum b ≤ 1) :
    |(Finset.range n).sum e| ≤ 1 := by
  calc
    |(Finset.range n).sum e|
      ≤ (Finset.range n).sum (fun j => |e j|) := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range n).sum b := by
        apply Finset.sum_le_sum
        intro j hj
        exact he j (lt_of_lt_of_le (Finset.mem_range.mp hj) hnK)
    _ ≤ (Finset.range K).sum b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hj) hnK)
        · intro j hjK _hjN
          exact hb0 j (Finset.mem_range.mp hjK)
    _ ≤ 1 := hbudget

theorem path_remainder_identity
    (x : ℕ → ℝ) (Gamma C : ℝ) (j : ℕ)
    (hx : x j ≠ 0)
    (rho : ℝ)
    (hrho :
      rho = x (j+1) - x j + Gamma + C / x j) :
    x (j+1) = x j - Gamma - C / x j + rho := by
  rw [hrho]
  ring

#print axioms finite_clock_error_bound
#print axioms path_remainder_identity

end YMUICV128.Section03.T011C
