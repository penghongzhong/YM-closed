import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T011B

theorem eta_summable_from_two_summable_errors
    (eta rho xinv2 : ℕ → ℝ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (heta : ∀ j, |eta j| ≤ C * (xinv2 j + |rho j|))
    (hx : Summable xinv2)
    (hrho : Summable (fun j => |rho j|))
    (hx0 : ∀ j, 0 ≤ xinv2 j) :
    Summable (fun j => |eta j|) := by
  have hmajor :
      Summable (fun j => C * (xinv2 j + |rho j|)) := by
    have hs : Summable (fun j => xinv2 j + |rho j|) :=
      hx.add hrho
    exact hs.mul_left C
  exact Summable.of_nonneg_of_le
    (fun _ => abs_nonneg _)
    heta hmajor

theorem corrected_clock_telescoping
    (Psi x eta : ℕ → ℝ)
    (K : ℕ)
    (hstep : ∀ j < K, Psi (j+1) - Psi j = -1 + eta j) :
    Psi K - Psi 0 = -(K : ℝ) + ∑ j in Finset.range K, eta j := by
  have hsum :
      ∑ j in Finset.range K, (Psi (j+1) - Psi j)
        =
      ∑ j in Finset.range K, (-1 + eta j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hstep j (Finset.mem_range.mp hj)
  have htel :
      ∑ j in Finset.range K, (Psi (j+1) - Psi j)
        = Psi K - Psi 0 := by
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [htel] at hsum
  simpa [Finset.sum_add_distrib] using hsum

#print axioms eta_summable_from_two_summable_errors
#print axioms corrected_clock_telescoping

end YMUICV128.Section03.T011B
