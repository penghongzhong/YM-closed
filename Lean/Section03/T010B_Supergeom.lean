import Mathlib
import Section03.T010A_Distance_GeometricTail

set_option autoImplicit false

namespace YMUICV128.Section03.T010B

theorem pow_ge_linear (L : ℝ) :
    ∀ n : ℕ, 1 ≤ n → L ≥ 2 → L ^ n ≥ L * n := by
  intro n hn hL
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n; simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hih := ih hn1
        have hL0 : 0 ≤ L := by linarith
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hl : (n : ℝ) + 1 ≤ (n : ℝ) * L := by nlinarith
        have hm := mul_le_mul_of_nonneg_left hl hL0
        calc
          L ^ (n + 1) = L ^ n * L := pow_succ L n
          _ ≥ (L * n) * L := mul_le_mul_of_nonneg_right hih hL0
          _ ≥ L * ((n : ℝ) + 1) := by nlinarith only [hm]
          _ = L * ((n + 1 : ℕ) : ℝ) := by norm_num

theorem supergeom_term_bound (L nu R : ℝ) (n : ℕ)
    (hL : 2 ≤ L) (hnu : 0 < nu) (hR : 0 < R) (hn : 1 ≤ n) :
    Real.exp (-nu * L ^ n * R) ≤ (Real.exp (-nu * L * R)) ^ n := by
  have hp := pow_ge_linear L n hn hL
  have hm := mul_le_mul_of_nonneg_left hp (mul_pos hnu hR).le
  have he : -nu * L ^ n * R ≤ -nu * (L * n) * R := by nlinarith only [hm]
  calc
    Real.exp (-nu * L ^ n * R) ≤ Real.exp (-nu * (L * n) * R) := Real.exp_le_exp.mpr he
    _ = (Real.exp (-nu * L * R)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem geometric_sum_from_one_le (q : ℝ) (K : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (Finset.range K).sum (fun n => q ^ (n + 1)) ≤ q / (1 - q) := by
  calc
    (Finset.range K).sum (fun n => q ^ (n + 1)) =
        q * (Finset.range K).sum (fun n => q ^ n) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          rw [pow_succ]
          ring
    _ ≤ q * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left (T010A.geometric_prefix_le q K hq0 hq1) hq0
    _ = q / (1 - q) := by ring

theorem supergeom_sum_bound (L nu R : ℝ) (K : ℕ)
    (hL : 2 ≤ L) (hnu : 0 < nu) (hR : 0 < R) :
    (Finset.range K).sum (fun n => Real.exp (-nu * L ^ (n + 1) * R)) ≤
      Real.exp (-nu * L * R) / (1 - Real.exp (-nu * L * R)) := by
  have hL0 : 0 < L := by linarith
  have hneg : -nu * L * R < 0 := by
    have h := mul_pos (mul_pos hnu hL0) hR
    nlinarith
  have hq1 : Real.exp (-nu * L * R) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  calc
    (Finset.range K).sum (fun n => Real.exp (-nu * L ^ (n + 1) * R)) ≤
        (Finset.range K).sum (fun n => (Real.exp (-nu * L * R)) ^ (n + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact supergeom_term_bound L nu R (n + 1) hL hnu hR (by omega)
    _ ≤ Real.exp (-nu * L * R) / (1 - Real.exp (-nu * L * R)) :=
      geometric_sum_from_one_le _ K (Real.exp_pos _).le hq1

#print axioms pow_ge_linear
#print axioms supergeom_term_bound
#print axioms geometric_sum_from_one_le
#print axioms supergeom_sum_bound

end YMUICV128.Section03.T010B
