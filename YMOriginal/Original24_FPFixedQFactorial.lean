import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Fixed-q finite-height FP enumeration: bypass the q label-orbit proof

The published unlabeled rooted-tree exponential enumeration uses
1/(n+1)! for n ordinary bulk vertices plus ONE named q polymer vertex.

The C29 Mayer two-root series uses 1/n!. For all n>=0,
(n+1) <= 2^n, so choosing a doubled bulk fugacity 2*lambda in
the positive augmented KP comparison absorbs this label deficit:
    lambda^n * eps / n! <= (2*lambda)^n * eps / (n+1)!.
This allows an exact fixed-q-slot injection with NO unproved
permutation-invariance lemma for every labeled spanning tree.

The physical smallness must then absorb this factor 2; no
instantaneous conclusion about the actual full FP series is asserted.
-/

/-- Finite combinatorial bound including n=0: n+1 ≤ 2^n. -/
theorem original24_succ_le_two_pow (n : ℕ) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ n := pow_pos (by norm_num) n
      omega

/-- The EXACT factorial cost of fixing q at one tagged position is
absorbed by doubling the real nonnegative bulk fugacity.

No hFP, tree enumeration, symmetry input, or source bound is used. -/
theorem original24_fixed_q_factorial_absorbed
    (n : ℕ) (lam eps weight : ℝ)
    (hlam : 0 ≤ lam) (heps : 0 ≤ eps) (hweight : 0 ≤ weight) :
    (lam ^ n * eps * weight) / (Nat.factorial n : ℝ) ≤
      ((2 * lam) ^ n * eps * weight) /
        (Nat.factorial (n + 1) : ℝ) := by
  have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
  have hfac' : 0 < (Nat.factorial (n + 1) : ℝ) := by positivity
  have hpow : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast original24_succ_le_two_pow n
  have hw : 0 ≤ lam ^ n * eps * weight :=
    mul_nonneg (mul_nonneg (pow_nonneg hlam n) heps) hweight
  have hscale :
      (lam ^ n * eps * weight) * (n + 1 : ℝ) ≤
        (lam ^ n * eps * weight) * (2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hpow hw
  have hfactorial : (Nat.factorial (n + 1) : ℝ) =
      (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  apply (div_le_div_iff₀ hfac hfac').mpr
  calc
    (lam ^ n * eps * weight) * (Nat.factorial (n + 1) : ℝ) =
        ((lam ^ n * eps * weight) * (n + 1 : ℝ)) *
          (Nat.factorial n : ℝ) := by rw [hfactorial]; ring
    _ ≤ ((lam ^ n * eps * weight) * (2 : ℝ) ^ n) *
          (Nat.factorial n : ℝ) :=
      mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _)
    _ = ((2 * lam) ^ n * eps * weight) *
          (Nat.factorial n : ℝ) := by rw [mul_pow]; ring

end YMUIC.Original24
