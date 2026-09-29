import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T011B

theorem eta_summable_from_two_summable_errors (eta rho xinv2 : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (heta : ∀ j, |eta j| ≤ C * (xinv2 j + |rho j|))
    (hx : Summable xinv2) (hrho : Summable (fun j => |rho j|))
    (hx0 : ∀ j, 0 ≤ xinv2 j) : Summable (fun j => |eta j|) := by
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) heta ((hx.add hrho).mul_left C)

theorem finite_difference_sum (Psi : ℕ → ℝ) (K : ℕ) :
    (Finset.range K).sum (fun j => Psi (j + 1) - Psi j) = Psi K - Psi 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem corrected_clock_telescoping (Psi x eta : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ j < K, Psi (j + 1) - Psi j = -1 + eta j) :
    Psi K - Psi 0 = -(K : ℝ) + (Finset.range K).sum (fun j => eta j) := by
  calc
    Psi K - Psi 0 = (Finset.range K).sum (fun j => Psi (j + 1) - Psi j) :=
      (finite_difference_sum Psi K).symm
    _ = (Finset.range K).sum (fun j => -1 + eta j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hstep j (Finset.mem_range.mp hj)
    _ = _ := by simp [Finset.sum_add_distrib]

theorem path_clock_telescoping (Psi : ℝ → ℝ) (x : ℕ → ℝ) (K : ℕ) :
    Psi (x K) - Psi (x 0) = -(K : ℝ) +
      (Finset.range K).sum (fun j => Psi (x (j + 1)) - Psi (x j) + 1) := by
  apply corrected_clock_telescoping (fun j => Psi (x j)) x
  intro j hj
  ring

#print axioms eta_summable_from_two_summable_errors
#print axioms finite_difference_sum
#print axioms corrected_clock_telescoping
#print axioms path_clock_telescoping

end YMUICV128.Section03.T011B
