import Mathlib

set_option autoImplicit false

/-!
# U2 rooted-tree majorant: KP scalar core

Standalone certificate for the scalar part of v133
`lem:root-tree-majorant`, equations `muchoice`, `KPweights`,
`clustersmallness`, and the final two inequalities in `childsum`.

This file does NOT yet prove the finite contact-counting inequality
  sum_{Y : Y ~_chi X} (...) <= N_chi * |X| * a_*.
That combinatorial counting step is isolated for the next certificate.
-/

namespace YMUICV128.Section03.T006A

def delta (kappa mu : ℝ) (cGeo : ℕ) : ℝ :=
  kappa - (cGeo : ℝ) * mu

noncomputable def ADelta (deltaValue : ℝ) (d : ℕ) : ℝ :=
  (deltaValue / 2) * (d : ℝ)

noncomputable def kpWeight
    (absZ kappa mu : ℝ) (cGeo d : ℕ) : ℝ :=
  absZ * Real.exp ((cGeo : ℝ) * mu * (d : ℝ))

theorem delta_pos_of_mu_lt_div
    {kappa mu : ℝ} {cGeo : ℕ}
    (hkappa : 0 < kappa)
    (hmu0 : 0 < mu)
    (hcGeo : 1 ≤ cGeo)
    (hmu : mu < kappa / (cGeo : ℝ)) :
    0 < delta kappa mu cGeo := by
  have hcGeoR : (0 : ℝ) < (cGeo : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcGeo)
  have hprod : mu * (cGeo : ℝ) < kappa :=
    (lt_div_iff₀ hcGeoR).mp hmu
  unfold delta
  nlinarith [hprod]

theorem delta_nonneg_of_pos
    {kappa mu : ℝ} {cGeo : ℕ}
    (hdelta : 0 < delta kappa mu cGeo) :
    0 ≤ delta kappa mu cGeo :=
  hdelta.le

theorem kp_exponent_identity
    (kappa mu : ℝ) (cGeo d : ℕ) :
    (cGeo : ℝ) * mu * (d : ℝ)
        + (delta kappa mu cGeo / 2) * (d : ℝ)
      =
    kappa * (d : ℝ)
        + (-(delta kappa mu cGeo) / 2) * (d : ℝ) := by
  unfold delta
  ring

theorem kp_weight_times_ADelta
    (absZ kappa mu : ℝ) (cGeo d : ℕ) :
    kpWeight absZ kappa mu cGeo d
        * Real.exp (ADelta (delta kappa mu cGeo) d)
      =
    absZ * Real.exp (kappa * (d : ℝ))
        * Real.exp ((-(delta kappa mu cGeo) / 2) * (d : ℝ)) := by
  unfold kpWeight ADelta
  rw [mul_assoc, ← Real.exp_add]
  rw [kp_exponent_identity]
  rw [Real.exp_add]
  ring

theorem half_delta_nonneg
    {deltaValue : ℝ}
    (hdelta : 0 ≤ deltaValue) :
    0 ≤ deltaValue / 2 := by
  positivity

theorem child_scalar_budget
    {Nchi cardX dX : ℕ}
    {aStar deltaValue : ℝ}
    (haStar : 0 ≤ aStar)
    (hdelta : 0 ≤ deltaValue)
    (hcard : cardX ≤ dX)
    (hsmall :
      (Nchi : ℝ) * aStar ≤ deltaValue / 2) :
    (Nchi : ℝ) * (cardX : ℝ) * aStar
      ≤ ADelta deltaValue dX := by
  have hcardR : (cardX : ℝ) ≤ (dX : ℝ) := by
    exact_mod_cast hcard
  have hhalf : 0 ≤ deltaValue / 2 :=
    half_delta_nonneg hdelta
  calc
    (Nchi : ℝ) * (cardX : ℝ) * aStar
        = ((Nchi : ℝ) * aStar) * (cardX : ℝ) := by ring
    _ ≤ (deltaValue / 2) * (cardX : ℝ) := by
      exact mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ (deltaValue / 2) * (dX : ℝ) := by
      exact mul_le_mul_of_nonneg_left hcardR hhalf
    _ = ADelta deltaValue dX := by
      rfl

theorem child_scalar_budget_from_mu_window
    {kappa mu aStar : ℝ}
    {cGeo Nchi cardX dX : ℕ}
    (hkappa : 0 < kappa)
    (hmu0 : 0 < mu)
    (hcGeo : 1 ≤ cGeo)
    (hmu : mu < kappa / (cGeo : ℝ))
    (haStar : 0 ≤ aStar)
    (hcard : cardX ≤ dX)
    (hsmall :
      (Nchi : ℝ) * aStar
        ≤ delta kappa mu cGeo / 2) :
    (Nchi : ℝ) * (cardX : ℝ) * aStar
      ≤ ADelta (delta kappa mu cGeo) dX := by
  exact child_scalar_budget
    haStar
    (delta_pos_of_mu_lt_div hkappa hmu0 hcGeo hmu).le
    hcard
    hsmall

#print axioms delta_pos_of_mu_lt_div
#print axioms kp_exponent_identity
#print axioms kp_weight_times_ADelta
#print axioms child_scalar_budget
#print axioms child_scalar_budget_from_mu_window

end YMUICV128.Section03.T006A
