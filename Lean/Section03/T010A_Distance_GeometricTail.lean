import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010A

theorem geometric_shift (q : ℝ) (n : ℕ) :
    q * (Finset.range n).sum (fun m => q ^ m) + 1 =
      (Finset.range (n + 1)).sum (fun m => q ^ m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ, pow_succ] at *
      nlinarith

theorem geometric_prefix_identity (q : ℝ) (n : ℕ) :
    (1 - q) * (Finset.range n).sum (fun m => q ^ m) = 1 - q ^ n := by
  have h := geometric_shift q n
  rw [Finset.sum_range_succ] at h
  nlinarith

theorem geometric_prefix_le (q : ℝ) (n : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (Finset.range n).sum (fun m => q ^ m) ≤ 1 / (1 - q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq1)).2
  have h := geometric_prefix_identity q n
  have hp := pow_nonneg hq0 n
  nlinarith

theorem support_recurrence_nat (q b : ℝ) (r : ℕ → ℝ) (j : ℕ)
    (hq : 0 ≤ q)
    (hrec : ∀ n < j, q * r n - b ≤ r (n + 1)) :
    q ^ j * r 0 - b * (Finset.range j).sum (fun m => q ^ m) ≤ r j := by
  revert hrec
  induction j with
  | zero => intro hrec; simp
  | succ j ih =>
      intro hrec
      have hi := ih (fun n hn => hrec n (by omega))
      have hm := mul_le_mul_of_nonneg_left hi hq
      have hs := geometric_shift q j
      calc
        q ^ (j + 1) * r 0 - b * (Finset.range (j + 1)).sum (fun m => q ^ m)
            = q * (q ^ j * r 0 - b * (Finset.range j).sum (fun m => q ^ m)) - b := by
                rw [← hs, pow_succ]
                ring
        _ ≤ q * r j - b := sub_le_sub_right hm b
        _ ≤ r (j + 1) := hrec j (by omega)

theorem support_recurrence_iterated (L b : ℝ) (r : ℕ → ℝ) (j : ℕ)
    (hL : 0 < L) (hrec : ∀ n, r (n + 1) ≥ L⁻¹ * r n - b) :
    r j ≥ L ^ (-(j : ℤ)) * r 0 -
      b * (Finset.range j).sum (fun m => L ^ (-(m : ℤ))) := by
  simpa only [zpow_neg, zpow_natCast, inv_pow] using
    support_recurrence_nat L⁻¹ b r j (inv_nonneg.mpr hL.le) (fun n _ => hrec n)

theorem distance_lower_bound_from_tail
    (L b : ℝ) (r : ℕ → ℝ) (K j : ℕ) (hL : 0 < L)
    (hrec : ∀ n, r (n + 1) ≥ L⁻¹ * r n - b)
    (htail : b * (Finset.range j).sum (fun m => L ^ (-(m : ℤ))) ≤ b * L / (L - 1))
    (hpow : L ^ (-(j : ℤ)) * r 0 =
      L ^ ((K : ℤ) - (j : ℤ)) * (L ^ (-(K : ℤ)) * r 0)) :
    r j ≥ L ^ ((K : ℤ) - (j : ℤ)) * (L ^ (-(K : ℤ)) * r 0) - b * L / (L - 1) := by
  have hi := support_recurrence_iterated L b r j hL hrec
  rw [hpow] at hi
  linarith

/-- Complete distance theorem: neither the geometric tail nor the power identity is an input. -/
theorem distance_lower_bound (L b : ℝ) (r : ℕ → ℝ) (K j : ℕ)
    (hL : 1 < L) (hb : 0 ≤ b) (hjK : j ≤ K)
    (hrec : ∀ n < K, L⁻¹ * r n - b ≤ r (n + 1)) :
    L ^ (K - j) * (L ^ (-(K : ℤ)) * r 0) - b * L / (L - 1) ≤ r j := by
  have hL0 : 0 < L := lt_trans (by norm_num) hL
  have hq0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hL0.le
  have hq1 : L⁻¹ < 1 := by
    simpa only [one_div] using (div_lt_one hL0).2 hL
  have hi := support_recurrence_nat L⁻¹ b r j hq0 (fun n hn => hrec n (by omega))
  have ht := mul_le_mul_of_nonneg_left (geometric_prefix_le L⁻¹ j hq0 hq1) hb
  have hc : b * (1 / (1 - L⁻¹)) = b * L / (L - 1) := by
    field_simp [hL0.ne', (sub_pos.mpr hL).ne'] <;> ring
  rw [hc] at ht
  have hp : L ^ ((K : ℤ) - (j : ℤ)) * L ^ (-(K : ℤ)) = L ^ (-(j : ℤ)) := by
    rw [← zpow_add₀ hL0.ne']
    congr 1
    ring
  have hz : ((K - j : ℕ) : ℤ) = (K : ℤ) - (j : ℤ) := Int.ofNat_sub hjK
  rw [← hz, zpow_natCast] at hp
  have hp' : L ^ (K - j) * (L ^ (-(K : ℤ)) * r 0) = (L⁻¹) ^ j * r 0 := by
    rw [← mul_assoc, hp]
    simp only [zpow_neg, zpow_natCast, inv_pow]
  rw [hp']
  linarith

#print axioms geometric_shift
#print axioms geometric_prefix_identity
#print axioms geometric_prefix_le
#print axioms support_recurrence_nat
#print axioms support_recurrence_iterated
#print axioms distance_lower_bound_from_tail
#print axioms distance_lower_bound

end YMUICV128.Section03.T010A
