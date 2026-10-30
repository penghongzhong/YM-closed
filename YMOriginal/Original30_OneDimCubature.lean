import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30

/-!
# Genuine one-dimensional lattice cubature uniform in box size

The physical lattice spacing a in (0,1] and all finite cutoffs N
satisfy the TRUE geometric inequality

  a * sum_{k=0}^{N-1} 1/(1+a*k)^2 <= 2.

This is not an assumed cubature budget. It follows by exact
telescoping of 1/(1+a*k). The upper bound is UNIFORM in
a -> 0 and N -> infinity; it is the first analytic ingredient
for eliminating the spurious finite-box R^4 loss in Original30
using Schwartz spatial decay on the actual a*Z^4 grid.

Unlike R^4 volume counting, this bound survives N*a->infinity.
-/

/-- One-step inverse-square cubature is dominated by the exact
decrease of a reciprocal geometric denominator. -/
theorem lattice_inverse_square_telescope_step
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    a / (1 + a * ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
      1 / (1 + a * (n : ℝ)) -
      1 / (1 + a * ((n + 1 : ℕ) : ℝ)) := by
  let u : ℝ := 1 + a * (n : ℝ)
  let v : ℝ := 1 + a * ((n + 1 : ℕ) : ℝ)
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hv_def : v = u + a := by
    dsimp [u, v]
    push_cast
    ring
  have huv : u ≤ v := by rw [hv_def]; linarith
  have hdenom : u * v ≤ v ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right huv hv.le]
  have hinv : 1 / (v ^ 2) ≤ 1 / (u * v) :=
    one_div_le_one_div_of_le (mul_pos hu hv) hdenom
  have hdiff : 1 / u - 1 / v = a / (u * v) := by
    field_simp [hu.ne', hv.ne']
    linarith [hv_def]
  change a / (v ^ 2) ≤ 1 / u - 1 / v
  calc
    a / v ^ 2 = a * (1 / v ^ 2) := by ring
    _ ≤ a * (1 / (u * v)) :=
      mul_le_mul_of_nonneg_left hinv ha.le
    _ = a / (u * v) := by ring
    _ = 1 / u - 1 / v := hdiff.symm

/-- Telescoping bound with exact boundary correction; no N-dependent
constant appears. -/
theorem lattice_inverse_square_prefix
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      a / (1 + a * (k : ℝ)) ^ 2) ≤
      a + 1 - 1 / (1 + a * (n : ℝ)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep := lattice_inverse_square_telescope_step a ha n
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range (n + 1),
          a / (1 + a * (k : ℝ)) ^ 2) +
          a / (1 + a * ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
            (a + 1 - 1 / (1 + a * (n : ℝ))) +
            (1 / (1 + a * (n : ℝ)) -
              1 / (1 + a * ((n + 1 : ℕ) : ℝ))) :=
                add_le_add ih hstep
        _ = a + 1 - 1 / (1 + a * ((n + 1 : ℕ) : ℝ)) := by ring

/-- The physical 1D normalized source weight is uniformly summable
for any lattice spacing 0<a<=1 and any finite lattice length N. -/
theorem lattice_inverse_square_uniform_all_cutoffs
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      a / (1 + a * (k : ℝ)) ^ 2) ≤ 2 := by
  cases N with
  | zero => simp
  | succ n =>
      have hbound := lattice_inverse_square_prefix a ha n
      have hinv : 0 ≤ 1 / (1 + a * (n : ℝ)) := by positivity
      linarith

end YMUIC.Original30
