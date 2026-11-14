import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original24: exact one-q labeled-source factorial normalization

The Fernández--Procacci planar-rooted-tree formula has
a symmetry factor 1/(m!) for m non-root vertices.
In a two-Wilson-root graph, there are exactly n bulk histories
and exactly ONE second source root q, so m=n+1.

There are exactly n+1 possible q labels among the non-root
vertices. By invariance of the positive tree weight under the
simultaneous relabeling of the non-root vertex positions,
summing over the unique-q label gives
  (n+1)/(n+1)! = 1/n!.
The original C29/ActualExactTwoRootMayerTerm factor 1/n! is
thus the correct symmetry factor, NOT 1/(n+1)!.

This theorem formally checks the factorial/label-position step.
It does not prove the required FP planar-tree equivalence or
the physical RG history index dictionary; those are separate.
-/

/-- The source labeling factor exactly restores the original
1/n! coefficient, with no factorial or n-dependent constant
lost when passing from the augmented q-species rooted trees
to the n+2-vertex original two-root graph. -/
theorem original24_unique_second_root_factorial
    (n : ℕ) (W : ℝ) :
    (∑ _qslot : Fin (n + 1),
      ((Nat.factorial (n + 1) : ℝ)⁻¹ * W)) =
    (Nat.factorial n : ℝ)⁻¹ * W := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by positivity
  have hfact :
      ((Nat.factorial (n + 1) : ℕ) : ℝ) =
        (n + 1 : ℝ) * ((Nat.factorial n : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  calc
    (∑ _qslot : Fin (n + 1),
      ((Nat.factorial (n + 1) : ℝ)⁻¹ * W)) =
      (n + 1 : ℝ) *
        ((Nat.factorial (n + 1) : ℝ)⁻¹ * W) := by
          simp [nsmul_eq_mul]
    _ = (Nat.factorial n : ℝ)⁻¹ * W := by
      rw [hfact]
      field_simp

/-- Exact normalization for a symmetric labeled family: for
each q label position, the weight equals the distinguished
0-slot weight after relabeling. This is the precise invariance
premise used in Fernández--Procacci Eq. (4.19)--(4.22).
The full FP tree combinatorics are not smuggled into this theorem. -/
theorem original24_symmetric_unique_q_label_factorial
    (n : ℕ)
    (weight : Fin (n + 1) → ℝ)
    (hSymmetric : ∀ k, weight k = weight 0) :
    (∑ k : Fin (n + 1),
      ((Nat.factorial (n + 1) : ℝ)⁻¹ * weight k)) =
    (Nat.factorial n : ℝ)⁻¹ * weight 0 := by
  calc
    (∑ k : Fin (n + 1),
      ((Nat.factorial (n + 1) : ℝ)⁻¹ * weight k)) =
      ∑ _k : Fin (n + 1),
        ((Nat.factorial (n + 1) : ℝ)⁻¹ * weight 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hSymmetric k]
    _ = (Nat.factorial n : ℝ)⁻¹ * weight 0 :=
      original24_unique_second_root_factorial n (weight 0)

end YMUIC.Original24
