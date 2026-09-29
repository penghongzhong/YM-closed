import Mathlib
import Section03.T011B_CorrectedClock_Summability

set_option autoImplicit false

namespace YMUICV128.Section03.T011E

theorem inverse_square_one_step (x y delta : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hd : 0 < delta) (hstep : delta ≤ x - y) :
    x⁻¹ * x⁻¹ ≤ (y⁻¹ - x⁻¹) / delta := by
  have hxy : y ≤ x := by linarith
  have hid : y⁻¹ - x⁻¹ = (x - y) / (x * y) := by
    field_simp [hx.ne', hy.ne'] <;> ring
  have hbase : delta / (x * x) ≤ y⁻¹ - x⁻¹ := by
    rw [hid]
    apply (div_le_div_iff₀ (mul_pos hx hx) (mul_pos hx hy)).2
    have h1 := mul_le_mul_of_nonneg_right hstep (mul_pos hx hy).le
    have h2 := mul_le_mul_of_nonneg_left hxy hx.le
    have h3 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hxy)
    exact h1.trans h3
  apply (le_div_iff₀ hd).2
  convert hbase using 1 <;> field_simp [hx.ne'] <;> ring

/-- A cutoff- and horizon-independent estimate derived from actual drift. -/
theorem inverse_square_prefix_bound (x : ℕ → ℝ) (K : ℕ) (xw delta : ℝ)
    (hxw : 0 < xw) (hd : 0 < delta)
    (hlower : ∀ j ≤ K, xw ≤ x j)
    (hstep : ∀ j < K, delta ≤ x j - x (j + 1)) :
    (Finset.range K).sum (fun j => (x j)⁻¹ * (x j)⁻¹) ≤ 1 / (delta * xw) := by
  have hpos (j : ℕ) (hj : j ≤ K) : 0 < x j := lt_of_lt_of_le hxw (hlower j hj)
  calc
    (Finset.range K).sum (fun j => (x j)⁻¹ * (x j)⁻¹) ≤
        (Finset.range K).sum (fun j => ((x (j + 1))⁻¹ - (x j)⁻¹) / delta) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjK := Finset.mem_range.mp hj
          exact inverse_square_one_step _ _ delta (hpos j (by omega))
            (hpos (j + 1) (by omega)) hd (hstep j hjK)
    _ = ((x K)⁻¹ - (x 0)⁻¹) / delta := by
      rw [← Finset.sum_div, T011B.finite_difference_sum (fun j => (x j)⁻¹) K]
    _ ≤ xw⁻¹ / delta := by
      apply div_le_div_of_nonneg_right _ hd.le
      have ht : (x K)⁻¹ ≤ xw⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hxw (hlower K le_rfl)
      have h0 : 0 ≤ (x 0)⁻¹ := inv_nonneg.mpr (hpos 0 (Nat.zero_le _)).le
      linarith
    _ = 1 / (delta * xw) := by ring

#print axioms inverse_square_one_step
#print axioms inverse_square_prefix_bound

end YMUICV128.Section03.T011E
