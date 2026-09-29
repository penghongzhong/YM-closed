import Mathlib

set_option autoImplicit false

/-!
# U2 rooted-tree majorant: first-root sum

Standalone certificate for v133 equation `firstrootsum`.

Assume a finite contact family of possible first bulk vertices X attached to
the external root.  If
  F_h(X) <= exp(A(X)),
  w(X) exp(A(X)) = q(X),
and the damped weight q has per-block activity norm at most a_act, then a
root neighbourhood of cardinality at most N_root gives

  sum_{X : root ~_chi X} w(X) F_h(X)
    <= N_root * a_act.

This is independent of the later tree-enumeration/exponential-formula step.
-/

namespace YMUICV128.Section03.T006E

theorem weighted_F_le_damped
    {Polymer : Type*}
    (weight A F damped : Polymer → ℝ)
    (hweight : ∀ X, 0 ≤ weight X)
    (hF : ∀ X, F X ≤ Real.exp (A X))
    (hidentity :
      ∀ X, weight X * Real.exp (A X) = damped X) :
    ∀ X, weight X * F X ≤ damped X := by
  intro X
  calc
    weight X * F X
        ≤ weight X * Real.exp (A X) :=
      mul_le_mul_of_nonneg_left (hF X) (hweight X)
    _ = damped X := hidentity X

theorem contact_sum_le_double_sum
    {Block Polymer : Type*}
    [Fintype Polymer]
    [DecidableEq Block]
    [DecidableEq Polymer]
    (Aroot : Finset Block)
    (contact : Finset Polymer)
    (through : Block → Finset Polymer)
    (q : Polymer → ℝ)
    (hq : ∀ X, 0 ≤ q X)
    (hcover :
      ∀ X ∈ contact,
        ∃ Δ ∈ Aroot, X ∈ through Δ) :
    (∑ X ∈ contact, q X)
      ≤
    ∑ Δ ∈ Aroot, ∑ X ∈ through Δ, q X := by
  classical
  calc
    (∑ X ∈ contact, q X)
        ≤
      ∑ X ∈ contact,
        ∑ Δ ∈ Aroot, if X ∈ through Δ then q X else 0 := by
      apply Finset.sum_le_sum
      intro X hX
      obtain ⟨Δ, hΔ, hXΔ⟩ := hcover X hX
      have hnonneg :
          ∀ Δ' ∈ Aroot,
            0 ≤ if X ∈ through Δ' then q X else 0 := by
        intro Δ' hΔ'
        by_cases hm : X ∈ through Δ'
        · simp [hm, hq X]
        · simp [hm]
      have hsingle := Finset.single_le_sum hnonneg hΔ
      simpa [hXΔ] using hsingle
    _ ≤
      ∑ X ∈ (Finset.univ : Finset Polymer),
        ∑ Δ ∈ Aroot, if X ∈ through Δ then q X else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ contact
      · intro X hXu hXnot
        exact Finset.sum_nonneg fun Δ hΔ => by
          by_cases hm : X ∈ through Δ
          · simp [hm, hq X]
          · simp [hm]
    _ =
      ∑ Δ ∈ Aroot, ∑ X ∈ through Δ, q X := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro Δ hΔ
      simp

theorem first_root_sum
    {Block Polymer : Type*}
    [Fintype Polymer]
    [DecidableEq Block]
    [DecidableEq Polymer]
    (Aroot : Finset Block)
    (contact : Finset Polymer)
    (through : Block → Finset Polymer)
    (weight A F damped : Polymer → ℝ)
    (aAct : ℝ)
    (Nroot : ℕ)
    (hweight : ∀ X, 0 ≤ weight X)
    (hdamped : ∀ X, 0 ≤ damped X)
    (haAct : 0 ≤ aAct)
    (hF : ∀ X, F X ≤ Real.exp (A X))
    (hidentity :
      ∀ X, weight X * Real.exp (A X) = damped X)
    (hcover :
      ∀ X ∈ contact,
        ∃ Δ ∈ Aroot, X ∈ through Δ)
    (hlocal :
      ∀ Δ,
        (∑ X ∈ through Δ, damped X) ≤ aAct)
    (hcard : Aroot.card ≤ Nroot) :
    (∑ X ∈ contact, weight X * F X)
      ≤ (Nroot : ℝ) * aAct := by
  have hpoint :
      ∀ X, weight X * F X ≤ damped X :=
    weighted_F_le_damped
      weight A F damped hweight hF hidentity
  calc
    (∑ X ∈ contact, weight X * F X)
        ≤ ∑ X ∈ contact, damped X := by
      exact Finset.sum_le_sum fun X hX => hpoint X
    _ ≤
      ∑ Δ ∈ Aroot,
        ∑ X ∈ through Δ, damped X :=
      contact_sum_le_double_sum
        Aroot contact through damped hdamped hcover
    _ ≤ ∑ _Δ ∈ Aroot, aAct := by
      exact Finset.sum_le_sum fun Δ hΔ => hlocal Δ
    _ = (Aroot.card : ℝ) * aAct := by
      simp [nsmul_eq_mul]
    _ ≤ (Nroot : ℝ) * aAct := by
      have hcardR : (Aroot.card : ℝ) ≤ (Nroot : ℝ) := by
        exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right hcardR haAct

#print axioms weighted_F_le_damped
#print axioms first_root_sum

end YMUICV128.Section03.T006E
