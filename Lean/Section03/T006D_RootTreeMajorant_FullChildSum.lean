import Mathlib

set_option autoImplicit false

/-!
# U2 rooted-tree majorant: full finite child-sum assembly

Standalone certificate for the load-bearing inequality `childsum`.

For a finite contact family of children Y of a parent X, assume:
* the contact family is covered by a finite block neighbourhood A;
* |A| <= N_chi |X|;
* through every block Delta, the unrooted weighted activity sum
    sum |z(Y)| exp(kappa d(Y))
  is at most a_*;
* N_chi a_* <= delta/2;
* |X| <= d(X);
* delta >= 0.

Then
  sum_contact |z(Y)| exp(kappa d(Y)) exp(-delta d(Y)/2)
    <= (delta/2) d(X) = A_delta(X).

This is exactly the quantitative content of equation `childsum`, with every
finite counting and damping step visible.
-/

namespace YMUICV128.Section03.T006D

noncomputable def baseWeight
    {Polymer : Type*}
    (absZ : Polymer → ℝ)
    (kappa : ℝ)
    (d : Polymer → ℕ)
    (Y : Polymer) : ℝ :=
  absZ Y * Real.exp (kappa * (d Y : ℝ))

noncomputable def dampedWeight
    {Polymer : Type*}
    (absZ : Polymer → ℝ)
    (kappa deltaValue : ℝ)
    (d : Polymer → ℕ)
    (Y : Polymer) : ℝ :=
  baseWeight absZ kappa d Y *
    Real.exp ((-deltaValue / 2) * (d Y : ℝ))

noncomputable def ADelta (deltaValue : ℝ) (dX : ℕ) : ℝ :=
  (deltaValue / 2) * (dX : ℝ)

theorem damping_factor_le_one
    {deltaValue : ℝ} (hdelta : 0 ≤ deltaValue) (m : ℕ) :
    Real.exp ((-deltaValue / 2) * (m : ℝ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  nlinarith

theorem dampedWeight_nonneg
    {Polymer : Type*}
    (absZ : Polymer → ℝ)
    (kappa deltaValue : ℝ)
    (d : Polymer → ℕ)
    (habsZ : ∀ Y, 0 ≤ absZ Y)
    (Y : Polymer) :
    0 ≤ dampedWeight absZ kappa deltaValue d Y := by
  unfold dampedWeight baseWeight
  exact mul_nonneg
    (mul_nonneg (habsZ Y) (Real.exp_pos _).le)
    (Real.exp_pos _).le

theorem dampedWeight_le_baseWeight
    {Polymer : Type*}
    (absZ : Polymer → ℝ)
    (kappa deltaValue : ℝ)
    (d : Polymer → ℕ)
    (habsZ : ∀ Y, 0 ≤ absZ Y)
    (hdelta : 0 ≤ deltaValue)
    (Y : Polymer) :
    dampedWeight absZ kappa deltaValue d Y
      ≤ baseWeight absZ kappa d Y := by
  unfold dampedWeight
  have hbase : 0 ≤ baseWeight absZ kappa d Y := by
    unfold baseWeight
    exact mul_nonneg (habsZ Y) (Real.exp_pos _).le
  calc
    baseWeight absZ kappa d Y *
        Real.exp ((-deltaValue / 2) * (d Y : ℝ))
        ≤ baseWeight absZ kappa d Y * 1 := by
          exact mul_le_mul_of_nonneg_left
            (damping_factor_le_one hdelta (d Y)) hbase
    _ = baseWeight absZ kappa d Y := by ring

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
      have hsingle := Finset.single_le_sum hnonneg hΔA
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

theorem through_damped_sum_le
    {Block Polymer : Type*}
    [DecidableEq Polymer]
    (through : Block → Finset Polymer)
    (absZ : Polymer → ℝ)
    (kappa deltaValue : ℝ)
    (d : Polymer → ℕ)
    (aStar : ℝ)
    (habsZ : ∀ Y, 0 ≤ absZ Y)
    (hdelta : 0 ≤ deltaValue)
    (hlocalBase :
      ∀ Δ,
        (∑ Y ∈ through Δ,
          baseWeight absZ kappa d Y) ≤ aStar) :
    ∀ Δ,
      (∑ Y ∈ through Δ,
        dampedWeight absZ kappa deltaValue d Y) ≤ aStar := by
  intro Δ
  calc
    (∑ Y ∈ through Δ,
        dampedWeight absZ kappa deltaValue d Y)
        ≤
      ∑ Y ∈ through Δ,
        baseWeight absZ kappa d Y := by
      exact Finset.sum_le_sum fun Y hY =>
        dampedWeight_le_baseWeight
          absZ kappa deltaValue d habsZ hdelta Y
    _ ≤ aStar := hlocalBase Δ

theorem full_childsum
    {Block Polymer : Type*}
    [Fintype Polymer]
    [DecidableEq Block]
    [DecidableEq Polymer]
    (A : Finset Block)
    (contact : Finset Polymer)
    (through : Block → Finset Polymer)
    (absZ : Polymer → ℝ)
    (kappa deltaValue aStar : ℝ)
    (d : Polymer → ℕ)
    (Nchi cardX dX : ℕ)
    (habsZ : ∀ Y, 0 ≤ absZ Y)
    (haStar : 0 ≤ aStar)
    (hdelta : 0 ≤ deltaValue)
    (hcover :
      ∀ Y ∈ contact,
        ∃ Δ ∈ A, Y ∈ through Δ)
    (hlocalBase :
      ∀ Δ,
        (∑ Y ∈ through Δ,
          baseWeight absZ kappa d Y) ≤ aStar)
    (hAcard : A.card ≤ Nchi * cardX)
    (hcard : cardX ≤ dX)
    (hsmall :
      (Nchi : ℝ) * aStar ≤ deltaValue / 2) :
    (∑ Y ∈ contact,
      dampedWeight absZ kappa deltaValue d Y)
      ≤ ADelta deltaValue dX := by
  have hdamped_nonneg :
      ∀ Y, 0 ≤ dampedWeight absZ kappa deltaValue d Y :=
    dampedWeight_nonneg absZ kappa deltaValue d habsZ
  have hthrough :
      ∀ Δ,
        (∑ Y ∈ through Δ,
          dampedWeight absZ kappa deltaValue d Y) ≤ aStar :=
    through_damped_sum_le
      through absZ kappa deltaValue d aStar
      habsZ hdelta hlocalBase
  have hcontact :
      (∑ Y ∈ contact,
        dampedWeight absZ kappa deltaValue d Y)
        ≤
      ∑ Δ ∈ A,
        ∑ Y ∈ through Δ,
          dampedWeight absZ kappa deltaValue d Y :=
    contact_sum_le_double_sum
      A contact through
      (dampedWeight absZ kappa deltaValue d)
      hdamped_nonneg hcover
  have hA :
      (∑ Δ ∈ A,
        ∑ Y ∈ through Δ,
          dampedWeight absZ kappa deltaValue d Y)
        ≤ (A.card : ℝ) * aStar := by
    calc
      (∑ Δ ∈ A,
        ∑ Y ∈ through Δ,
          dampedWeight absZ kappa deltaValue d Y)
          ≤ ∑ _Δ ∈ A, aStar := by
            exact Finset.sum_le_sum fun Δ hΔ => hthrough Δ
      _ = (A.card : ℝ) * aStar := by
            simp [nsmul_eq_mul]
  have hAcardR : (A.card : ℝ) ≤ (Nchi : ℝ) * (cardX : ℝ) := by
    exact_mod_cast hAcard
  have hcount :
      (A.card : ℝ) * aStar
        ≤ ((Nchi : ℝ) * (cardX : ℝ)) * aStar :=
    mul_le_mul_of_nonneg_right hAcardR haStar
  have hsmallX :
      ((Nchi : ℝ) * (cardX : ℝ)) * aStar
        ≤ (deltaValue / 2) * (cardX : ℝ) := by
    calc
      ((Nchi : ℝ) * (cardX : ℝ)) * aStar
          = ((Nchi : ℝ) * aStar) * (cardX : ℝ) := by ring
      _ ≤ (deltaValue / 2) * (cardX : ℝ) := by
          exact mul_le_mul_of_nonneg_right hsmall (by positivity)
  have hcardR : (cardX : ℝ) ≤ (dX : ℝ) := by
    exact_mod_cast hcard
  have hhalf : 0 ≤ deltaValue / 2 := by positivity
  calc
    (∑ Y ∈ contact,
      dampedWeight absZ kappa deltaValue d Y)
        ≤
      ∑ Δ ∈ A,
        ∑ Y ∈ through Δ,
          dampedWeight absZ kappa deltaValue d Y := hcontact
    _ ≤ (A.card : ℝ) * aStar := hA
    _ ≤ ((Nchi : ℝ) * (cardX : ℝ)) * aStar := hcount
    _ ≤ (deltaValue / 2) * (cardX : ℝ) := hsmallX
    _ ≤ (deltaValue / 2) * (dX : ℝ) :=
      mul_le_mul_of_nonneg_left hcardR hhalf
    _ = ADelta deltaValue dX := rfl

#print axioms damping_factor_le_one
#print axioms through_damped_sum_le
#print axioms full_childsum

end YMUICV128.Section03.T006D
