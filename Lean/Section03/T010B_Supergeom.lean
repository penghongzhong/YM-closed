import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010B

theorem pow_ge_linear
    (L : ℝ) (n : ℕ)
    (hL : 2 ≤ L)
    (hn : 1 ≤ n) :
    L ^ n ≥ L * n := by
  induction n using Nat.caseStrongInductionOn with
  | hz =>
      omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hih := ih n (by omega) hn1
        have hL0 : 0 ≤ L := le_trans (by norm_num) hL
        calc
          L ^ (n+1) = L^n * L := by ring
          _ ≥ (L * n) * L := by gcongr
          _ ≥ L * (n+1) := by
            nlinarith

theorem supergeom_finite_bound
    (L nu R : ℝ) (K : ℕ)
    (hL : 2 ≤ L)
    (hnu : 0 < nu)
    (hR : 0 < R) :
    ∑ n in Finset.Icc 1 K, Real.exp (-nu * L^n * R)
      ≤ Real.exp (-nu*L*R) / (1 - Real.exp (-nu*L*R)) := by
  let q : ℝ := Real.exp (-nu*L*R)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [hL, hnu, hR]
  have hterm :
      ∀ n ∈ Finset.Icc 1 K,
        Real.exp (-nu * L^n * R) ≤ q^n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hp := pow_ge_linear L n hL hn1
    have hcoef : -nu * L^n * R ≤ -nu * (L*n) * R := by
      have hpos : 0 < nu*R := mul_pos hnu hR
      nlinarith
    calc
      Real.exp (-nu * L^n * R)
          ≤ Real.exp (-nu * (L*n) * R) := Real.exp_le_exp.mpr hcoef
      _ = q^n := by
        dsimp [q]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hsum1 :
      ∑ n in Finset.Icc 1 K, Real.exp (-nu * L^n * R)
        ≤ ∑ n in Finset.Icc 1 K, q^n :=
    Finset.sum_le_sum hterm
  have hsum2 :
      ∑ n in Finset.Icc 1 K, q^n
        ≤ ∑ n in Finset.range (K+1), q^n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      exact Finset.mem_range.mpr (by omega)
    · intro n hn _hnot
      exact pow_nonneg hq0 _
  have hgeom :
      ∑ n in Finset.range (K+1), q^n
        ≤ 1 / (1-q) := by
    rw [geom_sum_eq]
    have hp0 : 0 ≤ q^(K+1) := pow_nonneg hq0 _
    have hd : 0 < 1-q := sub_pos.mpr hq1
    field_simp [ne_of_gt hd]
    nlinarith
  have htail :
      (∑ n in Finset.range (K+1), q^n) - 1
        ≤ q / (1-q) := by
    rw [geom_sum_eq]
    have hp0 : 0 ≤ q^(K+1) := pow_nonneg hq0 _
    have hd : 0 < 1-q := sub_pos.mpr hq1
    field_simp [ne_of_gt hd]
    nlinarith
  have hIcc :
      ∑ n in Finset.Icc 1 K, q^n
        ≤ (∑ n in Finset.range (K+1), q^n) - 1 := by
    have hdecomp :
        ∑ n in Finset.range (K+1), q^n
          = 1 + ∑ n in Finset.Icc 1 K, q^n := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rfl
    linarith
  calc
    ∑ n in Finset.Icc 1 K, Real.exp (-nu * L^n * R)
        ≤ ∑ n in Finset.Icc 1 K, q^n := hsum1
    _ ≤ (∑ n in Finset.range (K+1), q^n) - 1 := hIcc
    _ ≤ q / (1-q) := htail
    _ = Real.exp (-nu*L*R) /
        (1 - Real.exp (-nu*L*R)) := by
      rfl

#print axioms pow_ge_linear
#print axioms supergeom_finite_bound

end YMUICV128.Section03.T010B
