import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010B

theorem pow_ge_linear
    (L : ℝ) :
    ∀ n : ℕ, 1 ≤ n → L ≥ 2 → L ^ n ≥ L * n := by
  intro n hn hL
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hih := ih hn1
        have hL0 : 0 ≤ L := le_trans (by norm_num) hL
        calc
          L ^ (n+1) = L^n * L := by ring
          _ ≥ (L * n) * L := by gcongr
          _ ≥ L * (n+1) := by nlinarith

theorem supergeom_term_bound
    (L nu R : ℝ) (n : ℕ)
    (hL : 2 ≤ L)
    (hnu : 0 < nu)
    (hR : 0 < R)
    (hn : 1 ≤ n) :
    Real.exp (-nu * L^n * R)
      ≤ (Real.exp (-nu*L*R))^n := by
  have hp := pow_ge_linear L n hn hL
  have hcoef : -nu * L^n * R ≤ -nu * (L*n) * R := by
    have hpos : 0 < nu*R := mul_pos hnu hR
    nlinarith
  calc
    Real.exp (-nu * L^n * R)
      ≤ Real.exp (-nu * (L*n) * R) := Real.exp_le_exp.mpr hcoef
    _ = (Real.exp (-nu*L*R))^n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

#print axioms pow_ge_linear
#print axioms supergeom_term_bound

end YMUICV128.Section03.T010B
