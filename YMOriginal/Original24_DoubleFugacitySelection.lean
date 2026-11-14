import Mathlib

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Two fugacities recover the mandatory O(aAct) factor in two-root cluster sums

The second source root q is allowed to be an arbitrary-degree hub
rather than a leaf. A positive q-fugacity eps marks EXACTLY ONE q
vertex, and an independent bulk fugacity lam marks at least ONE
physical bulk polymer (the original no-root-root-edge condition).

A uniform augmented KP/FP bound for the fully doped (lam,eps)
tree family then implies a bound for the exact one-q, at-least-one-
bulk subfamily by dividing by lam*eps. Choosing lam of order
1/aAct converts this into the original required O(aAct) gain.

This finite combinatorial statement is fully proved; the remaining
model step is the actual FP enumeration identifying the full
extended n+2-vertex physical tree family with this doped family.
No arbitrary connected-Ursell output bound is a hypothesis.
-/

/-- A strictly nonnegative double-fugacity tree family:
the one-q and >=1-bulk part cannot exceed the positive full
doped family after multiplication by lam*eps. -/
theorem one_q_nonempty_bulk_le_double_fugacity
    {Tree : Type*} [DecidableEq Tree]
    (trees : Finset Tree)
    (bulkCount qCount : Tree → ℕ)
    (weight : Tree → ℝ)
    (hweight : ∀ T, 0 ≤ weight T)
    (lam eps : ℝ) (hlam : 1 ≤ lam) (heps : 0 ≤ eps) :
    (lam * eps) *
      (∑ T ∈ trees.filter
        (fun T => 1 ≤ bulkCount T ∧ qCount T = 1), weight T) ≤
      ∑ T ∈ trees,
        weight T * lam ^ bulkCount T * eps ^ qCount T := by
  classical
  let selected : Finset Tree :=
    trees.filter (fun T => 1 ≤ bulkCount T ∧ qCount T = 1)
  have hsubset : selected ⊆ trees :=
    Finset.filter_subset _ _
  have hlam0 : 0 ≤ lam := by linarith
  have hselected (T : Tree) (hT : T ∈ selected) :
      lam * eps * weight T ≤
        weight T * lam ^ bulkCount T * eps ^ qCount T := by
    have hc := (Finset.mem_filter.mp hT).2
    have hq : qCount T = 1 := hc.2
    have hb : 1 ≤ bulkCount T := hc.1
    have hpositive : bulkCount T ≠ 0 := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hpositive
    have hpow : lam ≤ lam ^ bulkCount T := by
      rw [hk, pow_succ]
      have hPowOne : 1 ≤ lam ^ k := one_le_pow₀ hlam
      calc
        lam = lam * 1 := by ring
        _ ≤ lam * lam ^ k :=
          mul_le_mul_of_nonneg_left hPowOne hlam0
        _ = lam ^ k * lam := by ring
    have hscale : lam * eps ≤ lam ^ bulkCount T * eps :=
      mul_le_mul_of_nonneg_right hpow heps
    calc
      lam * eps * weight T = weight T * (lam * eps) := by ring
      _ ≤ weight T * (lam ^ bulkCount T * eps) :=
        mul_le_mul_of_nonneg_left hscale (hweight T)
      _ = weight T * lam ^ bulkCount T * eps ^ qCount T := by
        rw [hq, pow_one]
        ring
  have hterm (T : Tree) :
      0 ≤ weight T * lam ^ bulkCount T * eps ^ qCount T := by
    exact mul_nonneg
      (mul_nonneg (hweight T) (pow_nonneg hlam0 _))
      (pow_nonneg heps _)
  calc
    (lam * eps) *
        (∑ T ∈ trees.filter
          (fun T => 1 ≤ bulkCount T ∧ qCount T = 1), weight T) =
      ∑ T ∈ selected, lam * eps * weight T := by
        dsimp [selected]
        rw [Finset.mul_sum]
    _ ≤ ∑ T ∈ selected,
        weight T * lam ^ bulkCount T * eps ^ qCount T :=
      Finset.sum_le_sum (fun T hT => hselected T hT)
    _ ≤ ∑ T ∈ trees,
        weight T * lam ^ bulkCount T * eps ^ qCount T :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun T hT hnot => hterm T)

/-- EXACT extraction of the marked one-q, nonempty-bulk series
from ANY verified complete augmented positive tree-family bound.
Unlike one-fugacity extraction, the extra lam factor allows
the original O(aAct) dependence to be recovered. -/
theorem one_q_nonempty_bulk_from_doped_majorant
    {Tree : Type*} [DecidableEq Tree]
    (trees : Finset Tree)
    (bulkCount qCount : Tree → ℕ)
    (weight : Tree → ℝ)
    (hweight : ∀ T, 0 ≤ weight T)
    (lam eps M : ℝ) (hlam : 1 ≤ lam) (heps : 0 < eps)
    (hfull :
      (∑ T ∈ trees,
        weight T * lam ^ bulkCount T * eps ^ qCount T) ≤ M) :
    (∑ T ∈ trees.filter
      (fun T => 1 ≤ bulkCount T ∧ qCount T = 1), weight T) ≤
        M / (lam * eps) := by
  have hlam0 : 0 < lam := by linarith
  apply (le_div_iff₀ (mul_pos hlam0 heps)).mpr
  calc
    (∑ T ∈ trees.filter
      (fun T => 1 ≤ bulkCount T ∧ qCount T = 1), weight T) *
        (lam * eps) =
      (lam * eps) * (∑ T ∈ trees.filter
        (fun T => 1 ≤ bulkCount T ∧ qCount T = 1), weight T) := by ring
    _ ≤ M :=
      (one_q_nonempty_bulk_le_double_fugacity
        trees bulkCount qCount weight hweight lam eps hlam heps.le).trans hfull

end YMUIC.Original24
