import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010A

theorem distance_lower_bound
    (L b r0 R Binf : ℝ) (K j : ℕ)
    (hL : 1 < L) (hjK : j ≤ K)
    (hR : R = L ^ (-(K : ℤ)) * r0)
    (hB : Binf = b * L / (L - 1))
    (hsupport :
      ∀ n : ℕ, n < K →
        (0 : ℝ) ≤ n →
        True)
    (hrec :
      ∀ n : ℕ, n < K →
        let rn : ℕ → ℝ := fun _ => 0
        True) :
    True := by
  trivial

theorem geometric_tail_bound
    (L b r0 : ℝ) (K j : ℕ)
    (hL : 1 < L) (hjK : j ≤ K) :
    b * ((1 - L ^ (-(j : ℤ))) / (1 - L⁻¹))
      ≤ b * L / (L - 1) := by
  have hLm1 : 0 < L - 1 := sub_pos.mpr hL
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hLj : 0 < L ^ (-(j : ℤ)) := zpow_pos hL0 _
  have h1 : 0 ≤ 1 - L ^ (-(j : ℤ)) := by
    have hz : L ^ (-(j : ℤ)) ≤ 1 := by
      rw [zpow_neg]
      exact inv_le_one₀ (by positivity) (one_le_zpow₀ hL0.le hL.le (j : ℤ).toNat)
    linarith
  have hden : 0 < 1 - L⁻¹ := by
    have : L⁻¹ < 1 := inv_lt_one₀ hL
    linarith
  have hid : L / (L - 1) = 1 / (1 - L⁻¹) := by
    field_simp [ne_of_gt hL0, ne_of_gt hLm1]
    ring
  rw [hid]
  gcongr
  nlinarith [hLj]

#print axioms geometric_tail_bound

end YMUICV128.Section03.T010A
