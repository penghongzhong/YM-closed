import Mathlib

set_option autoImplicit false

/-!
# v133 U2: external-root multiplier estimate

For real W with 0 ≤ W ≤ 4, complex source s with ‖s‖ ≤ r, r ≥ 0:
  ‖exp (s W) - 1‖ ≤ exp (4 r) - 1.

This is the exact pointwise estimate underlying equation (Kr).
-/

namespace YMUICV128.Section03

noncomputable def rootMultiplier (s : ℂ) (W : ℝ) : ℂ :=
  Complex.exp (s * (W : ℂ)) - 1

noncomputable def sourceConstant (r : ℝ) : ℝ :=
  Real.exp (4 * r) - 1

theorem norm_exp_sub_one_le_exp_norm_sub_one (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
  simpa using
    (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1)

theorem source_argument_norm_bound
    {r W : ℝ} (hr : 0 ≤ r) (hW0 : 0 ≤ W) (hW4 : W ≤ 4)
    (s : ℂ) (hs : ‖s‖ ≤ r) :
    ‖s * (W : ℂ)‖ ≤ 4 * r := by
  have hnormW : ‖(W : ℂ)‖ = W := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0]
  rw [norm_mul, hnormW]
  nlinarith [norm_nonneg s]

theorem rootMultiplier_bound
    {r W : ℝ} (hr : 0 ≤ r) (hW0 : 0 ≤ W) (hW4 : W ≤ 4)
    (s : ℂ) (hs : ‖s‖ ≤ r) :
    ‖rootMultiplier s W‖ ≤ sourceConstant r := by
  have hseries :
      ‖Complex.exp (s * (W : ℂ)) - 1‖
        ≤ Real.exp ‖s * (W : ℂ)‖ - 1 :=
    norm_exp_sub_one_le_exp_norm_sub_one _
  have hx : ‖s * (W : ℂ)‖ ≤ 4 * r :=
    source_argument_norm_bound hr hW0 hW4 s hs
  unfold rootMultiplier sourceConstant
  exact hseries.trans (sub_le_sub_right (Real.exp_le_exp.mpr hx) 1)

theorem sourceConstant_nonneg
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ sourceConstant r := by
  unfold sourceConstant
  have h : 1 ≤ Real.exp (4 * r) := by
    simpa using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 4 * r)
  linarith

#print axioms norm_exp_sub_one_le_exp_norm_sub_one
#print axioms source_argument_norm_bound
#print axioms rootMultiplier_bound
#print axioms sourceConstant_nonneg

end YMUICV128.Section03
