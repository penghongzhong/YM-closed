import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010A

theorem support_recurrence_iterated
    (L b : ℝ) (r : ℕ → ℝ)
    (j : ℕ)
    (hL : 0 < L)
    (hrec : ∀ n, r (n+1) ≥ L⁻¹ * r n - b) :
    r j ≥ L ^ (-(j : ℤ)) * r 0
      - b * ∑ m in Finset.range j, L ^ (-(m : ℤ)) := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have hj := hrec j
      calc
        r (j+1) ≥ L⁻¹ * r j - b := hj
        _ ≥ L⁻¹ *
              (L ^ (-(j : ℤ)) * r 0
                - b * ∑ m in Finset.range j, L ^ (-(m : ℤ))) - b := by
              gcongr
              positivity
        _ = L ^ (-((j+1 : ℕ) : ℤ)) * r 0
              - b * ∑ m in Finset.range (j+1), L ^ (-(m : ℤ)) := by
              rw [Finset.sum_range_succ]
              field_simp [ne_of_gt hL]
              ring

theorem geometric_partial_sum_le
    (L b : ℝ) (j : ℕ)
    (hL : 1 < L)
    (hb : 0 ≤ b) :
    b * ∑ m in Finset.range j, L ^ (-(m : ℤ))
      ≤ b * (L / (L - 1)) := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hq0 : 0 ≤ L⁻¹ := (inv_nonneg.mpr hL0.le)
  have hq1 : L⁻¹ < 1 := inv_lt_one₀ hL
  have hsum :
      ∑ m in Finset.range j, L ^ (-(m : ℤ))
        ≤ 1 / (1 - L⁻¹) := by
    have hgeom :
        ∑ m in Finset.range j, (L⁻¹) ^ m
          ≤ 1 / (1 - L⁻¹) := by
      rw [geom_sum_eq]
      have hpow : 0 ≤ (L⁻¹) ^ j := pow_nonneg hq0 _
      have hden : 0 < 1 - L⁻¹ := sub_pos.mpr hq1
      field_simp [ne_of_gt hden]
      nlinarith
    simpa [zpow_neg, inv_pow] using hgeom
  have hid : 1 / (1 - L⁻¹) = L / (L - 1) := by
    field_simp [ne_of_gt hL0, sub_ne_zero.mpr hL.ne']
    ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hsum hb

theorem distance_lower_bound
    (L b : ℝ) (r : ℕ → ℝ)
    (K j : ℕ)
    (hL : 1 < L)
    (hb : 0 ≤ b)
    (hjK : j ≤ K)
    (hrec : ∀ n, r (n+1) ≥ L⁻¹ * r n - b) :
    r j ≥
      L ^ ((K : ℤ) - (j : ℤ)) *
        (L ^ (-(K : ℤ)) * r 0)
      - b * L / (L - 1) := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hi := support_recurrence_iterated L b r j hL0 hrec
  have hs := geometric_partial_sum_le L b j hL hb
  have hpow :
      L ^ (-(j : ℤ)) * r 0
        =
      L ^ ((K : ℤ) - (j : ℤ)) *
        (L ^ (-(K : ℤ)) * r 0) := by
    rw [← zpow_add₀ (ne_of_gt hL0)]
    congr 2
    ring
  rw [hpow] at hi
  linarith

#print axioms support_recurrence_iterated
#print axioms geometric_partial_sum_le
#print axioms distance_lower_bound

end YMUICV128.Section03.T010A
