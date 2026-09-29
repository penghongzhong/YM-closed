import Mathlib

set_option autoImplicit false

/-!
# U2 rooted-tree majorant: finite-height recursion

Standalone certificate for v133
`treeRecursion` -> `treeRecursionBound`.

Given a finite child set C(X), nonnegative weights w, and a nonnegative
barrier A satisfying

  sum_{Y in C(X)} w(Y) exp(A(Y)) <= A(X),

define
  F_0(X) = 1,
  F_{h+1}(X) = exp (sum_{Y in C(X)} w(Y) F_h(Y)).

Then F_h(X) <= exp(A(X)) for every finite height h.
-/

namespace YMUICV128.Section03.T006C

noncomputable def treeMajorant
    {Polymer : Type*}
    [DecidableEq Polymer]
    (children : Polymer → Finset Polymer)
    (weight : Polymer → ℝ) :
    ℕ → Polymer → ℝ
  | 0, _ => 1
  | h + 1, X =>
      Real.exp
        (∑ Y ∈ children X,
          weight Y * treeMajorant children weight h Y)

theorem treeMajorant_zero
    {Polymer : Type*}
    [DecidableEq Polymer]
    (children : Polymer → Finset Polymer)
    (weight : Polymer → ℝ)
    (X : Polymer) :
    treeMajorant children weight 0 X = 1 := by
  rfl

theorem treeMajorant_succ
    {Polymer : Type*}
    [DecidableEq Polymer]
    (children : Polymer → Finset Polymer)
    (weight : Polymer → ℝ)
    (h : ℕ)
    (X : Polymer) :
    treeMajorant children weight (h + 1) X
      =
    Real.exp
      (∑ Y ∈ children X,
        weight Y * treeMajorant children weight h Y) := by
  rfl

theorem treeMajorant_bound
    {Polymer : Type*}
    [DecidableEq Polymer]
    (children : Polymer → Finset Polymer)
    (weight A : Polymer → ℝ)
    (hweight : ∀ Y, 0 ≤ weight Y)
    (hA : ∀ X, 0 ≤ A X)
    (hchild :
      ∀ X,
        (∑ Y ∈ children X,
          weight Y * Real.exp (A Y))
          ≤ A X) :
    ∀ h X,
      treeMajorant children weight h X
        ≤ Real.exp (A X) := by
  intro h
  induction h with
  | zero =>
      intro X
      simp only [treeMajorant_zero]
      exact Real.one_le_exp_iff.mpr (hA X)
  | succ h ih =>
      intro X
      rw [treeMajorant_succ]
      apply Real.exp_le_exp.mpr
      calc
        (∑ Y ∈ children X,
            weight Y * treeMajorant children weight h Y)
            ≤
          ∑ Y ∈ children X,
            weight Y * Real.exp (A Y) := by
          apply Finset.sum_le_sum
          intro Y hY
          exact mul_le_mul_of_nonneg_left (ih Y) (hweight Y)
        _ ≤ A X := hchild X

theorem treeMajorant_nonneg
    {Polymer : Type*}
    [DecidableEq Polymer]
    (children : Polymer → Finset Polymer)
    (weight : Polymer → ℝ)
    (h : ℕ)
    (X : Polymer) :
    0 ≤ treeMajorant children weight h X := by
  cases h with
  | zero =>
      simp [treeMajorant]
  | succ h =>
      exact (Real.exp_pos _).le

#print axioms treeMajorant_bound
#print axioms treeMajorant_nonneg

end YMUICV128.Section03.T006C
