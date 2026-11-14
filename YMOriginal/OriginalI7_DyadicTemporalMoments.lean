import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.I7Sparse

/-!
# One physical transfer: dyadic-time exponential moments suffice for I7

This lemma relaxes the unproved physical Yang--Mills input from ALL
temporal separations to the sparse series n = 2^k.

Only scalar spectral-moment arithmetic is established in this file;
hJensen is the positive-transfer Jensen inequality and hDecay is
explicitly a physical Wilson autocorrelation premise. Neither is
proved for actual four-dimensional SU(2) Wilson dynamics here.

The common rate q is chosen BEFORE the regulator and Wilson word.
The finite amplitude C may depend on each word and regulator.
-/

/-- The dyadic exponential-moment majorant forces the same rate at n=1.
One does not need the bound at every positive integer. -/
theorem dyadic_power_bound_forces_rate
    (x q C : ℝ) (hq : 0 < q)
    (hdyadic : ∀ k : ℕ, x ^ (2 ^ k) ≤ C * q ^ (2 ^ k)) :
    x ≤ q := by
  by_contra h
  have hqx : q < x := lt_of_not_ge h
  have hr : 1 < x / q := (one_lt_div hq).2 hqx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hr
  have hindex : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hone : 1 ≤ 2 ^ k := by positivity
      calc
        k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left hone _
        _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hpower :
      (x / q) ^ n ≤ (x / q) ^ (2 ^ n) :=
    pow_le_pow_right₀ hr.le (hindex n)
  have hqpow : 0 < q ^ (2 ^ n) := pow_pos hq _
  have hbound : (x / q) ^ (2 ^ n) ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ hqpow).2 (hdyadic n)
  exact (not_lt_of_ge (hpower.trans hbound)) hn

/-- Jensen moment convexity on ONLY dyadic indices plus dyadic
exponential decay yields a full one-step contraction.

The moments are general real values; physical validity requires the
same nonnegative self-adjoint Wilson/OS transfer for all powers.
-/
theorem dyadic_moment_decay_forces_one_step
    (q m0 m1 : ℝ) (hq : 0 < q) (hm0 : 0 < m0)
    (moments : ℕ → ℝ)
    (hJensen : ∀ k : ℕ,
      (m1 / m0) ^ (2 ^ k) ≤ moments (2 ^ k) / m0)
    (hDecay : ∃ C : ℝ, ∀ k : ℕ,
      moments (2 ^ k) ≤ C * q ^ (2 ^ k)) :
    m1 ≤ q * m0 := by
  obtain ⟨C, hC⟩ := hDecay
  have hPowers :
      ∀ k : ℕ,
        (m1 / m0) ^ (2 ^ k) ≤
          (C / m0) * q ^ (2 ^ k) := by
    intro k
    calc
      (m1 / m0) ^ (2 ^ k) ≤ moments (2 ^ k) / m0 :=
        hJensen k
      _ ≤ (C * q ^ (2 ^ k)) / m0 :=
        div_le_div_of_nonneg_right (hC k) hm0.le
      _ = (C / m0) * q ^ (2 ^ k) := by ring
  have hrate := dyadic_power_bound_forces_rate
    (m1 / m0) q (C / m0) hq hPowers
  exact (div_le_iff₀ hm0).1 hrate

#print axioms dyadic_power_bound_forces_rate
#print axioms dyadic_moment_decay_forces_one_step

end YMUIC.I7Sparse
