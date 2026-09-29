import Mathlib

set_option autoImplicit false

/-!
# U2 rooted-tree majorant: finite contact counting

This certificate isolates the combinatorial first inequality in v133
`childsum`.

If every child object in a finite contact set is covered by at least one block
in a finite neighbourhood A, and the weighted activity sum through each block
is at most a, then the total child weight is at most |A| a, hence at most
N_chi a when |A| <= N_chi.

No KP exponential algebra is used here; that is T006A.
-/

namespace YMUICV128.Section03.T006B

theorem contact_sum_le_double_sum
    {Block Polymer : Type*}
    [Fintype Polymer]
    [DecidableEq Block]
    [DecidableEq Polymer]
    (A : Finset Block)
    (contact : Finset Polymer)
    (through : Block → Finset Polymer)
    (weight : Polymer → ℝ)
    (hweight : ∀ Y, 0 ≤ weight Y)
    (hcover :
      ∀ Y ∈ contact,
        ∃ Δ ∈ A, Y ∈ through Δ) :
    (∑ Y ∈ contact, weight Y)
      ≤
    ∑ Δ ∈ A, ∑ Y ∈ through Δ, weight Y := by
  classical
  calc
    (∑ Y ∈ contact, weight Y)
        ≤
      ∑ Y ∈ contact,
        ∑ Δ ∈ A, if Y ∈ through Δ then weight Y else 0 := by
      apply Finset.sum_le_sum
      intro Y hY
      obtain ⟨Δ, hΔA, hYΔ⟩ := hcover Y hY
      have hnonneg :
          ∀ Δ' ∈ A,
            0 ≤ if Y ∈ through Δ' then weight Y else 0 := by
        intro Δ' hΔ'
        by_cases hmem : Y ∈ through Δ'
        · simp [hmem, hweight Y]
        · simp [hmem]
      have hsingle :=
        Finset.single_le_sum hnonneg hΔA
      simpa [hYΔ] using hsingle
    _ ≤
      ∑ Y ∈ (Finset.univ : Finset Polymer),
        ∑ Δ ∈ A, if Y ∈ through Δ then weight Y else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ contact
      · intro Y hYuniv hYnot
        exact Finset.sum_nonneg fun Δ hΔ => by
          by_cases hmem : Y ∈ through Δ
          · simp [hmem, hweight Y]
          · simp [hmem]
    _ =
      ∑ Δ ∈ A, ∑ Y ∈ through Δ, weight Y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro Δ hΔ
      simp

theorem contact_sum_le_card_mul
    {Block Polymer : Type*}
    [Fintype Polymer]
    [DecidableEq Block]
    [DecidableEq Polymer]
    (A : Finset Block)
    (contact : Finset Polymer)
    (through : Block → Finset Polymer)
    (weight : Polymer → ℝ)
    (a : ℝ)
    (hweight : ∀ Y, 0 ≤ weight Y)
    (hcover :
      ∀ Y ∈ contact,
        ∃ Δ ∈ A, Y ∈ through Δ)
    (hlocal :
      ∀ Δ ∈ A,
        (∑ Y ∈ through Δ, weight Y) ≤ a) :
    (∑ Y ∈ contact, weight Y)
      ≤ (A.card : ℝ) * a := by
  calc
    (∑ Y ∈ contact, weight Y)
        ≤ ∑ Δ ∈ A, ∑ Y ∈ through Δ, weight Y :=
      contact_sum_le_double_sum
        A contact through weight hweight hcover
    _ ≤ ∑ _Δ ∈ A, a := by
      exact Finset.sum_le_sum fun Δ hΔ => hlocal Δ hΔ
    _ = (A.card : ℝ) * a := by
      simp [nsmul_eq_mul]

theorem contact_sum_le_Nchi_mul
    {Block Polymer : Type*}
    [Fintype Polymer]
    [DecidableEq Block]
    [DecidableEq Polymer]
    (A : Finset Block)
    (contact : Finset Polymer)
    (through : Block → Finset Polymer)
    (weight : Polymer → ℝ)
    (a : ℝ)
    (Nchi : ℕ)
    (hweight : ∀ Y, 0 ≤ weight Y)
    (ha : 0 ≤ a)
    (hcover :
      ∀ Y ∈ contact,
        ∃ Δ ∈ A, Y ∈ through Δ)
    (hlocal :
      ∀ Δ ∈ A,
        (∑ Y ∈ through Δ, weight Y) ≤ a)
    (hcard : A.card ≤ Nchi) :
    (∑ Y ∈ contact, weight Y)
      ≤ (Nchi : ℝ) * a := by
  have h₁ :=
    contact_sum_le_card_mul
      A contact through weight a hweight hcover hlocal
  have hcardR : (A.card : ℝ) ≤ (Nchi : ℝ) := by
    exact_mod_cast hcard
  exact h₁.trans (mul_le_mul_of_nonneg_right hcardR ha)

#print axioms contact_sum_le_double_sum
#print axioms contact_sum_le_card_mul
#print axioms contact_sum_le_Nchi_mul

end YMUICV128.Section03.T006B
