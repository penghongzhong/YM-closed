import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section04.T012E

theorem drift_segment (x : ℕ → ℝ) (delta : ℝ) (K : ℕ)
    (hstep : ∀ j < K, x (j + 1) ≤ x j - delta) (i n : ℕ)
    (hin : i + n ≤ K) : x (i + n) ≤ x i - (n : ℝ) * delta := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := ih (by omega)
      have hs := hstep (i + n) (by omega)
      simp only [Nat.add_succ, Nat.cast_add, Nat.cast_one] at *
      linarith

theorem first_exit_exclusion (x : ℕ → ℝ) (K : ℕ) (xs delta : ℝ)
    (hd : 0 < delta) (hstep : ∀ j < K, x (j + 1) ≤ x j - delta)
    (hhit : x K = xs) : (∀ j < K, xs < x j) ∧ x K = xs := by
  refine ⟨?_, hhit⟩
  intro j hj
  have hsum : j + (K - j) = K := Nat.add_sub_of_le (by omega)
  have h := drift_segment x delta K hstep j (K - j) (by omega)
  rw [hsum, hhit] at h
  have hpos : (0 : ℝ) < ((K - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < K - j by omega)
  have hm := mul_pos hpos hd
  linarith

#print axioms drift_segment
#print axioms first_exit_exclusion

end YMUICV128.Section04.T012E
