import Mathlib

set_option autoImplicit false

/-!
# U2 marked-shell theorem: three-channel bound

Internal algebraic certificate for the paper decomposition
  K = K_sf + K_R + K_R'
with
  alpha = A_sf + g^kappa0 + exp(-p0(g))
and the explicit common shell constant
  C_shell = max C_sf C_lf.
-/

namespace YMUICV128.Section03.T009A

noncomputable def shellConstant (Csf Clf : ℝ) : ℝ :=
  max Csf Clf

noncomputable def shellActivity (A g e : ℝ) : ℝ :=
  A + g + e

theorem shellConstant_nonneg
    {Csf Clf : ℝ}
    (hCsf : 0 ≤ Csf) (hClf : 0 ≤ Clf) :
    0 ≤ shellConstant Csf Clf := by
  exact le_trans hCsf (le_max_left _ _)

theorem three_channel_bound
    (xsf xR xRp : ℂ)
    (Csf Clf A g e weight : ℝ)
    (hCsf : 0 ≤ Csf) (hClf : 0 ≤ Clf)
    (hA : 0 ≤ A) (hg : 0 ≤ g) (he : 0 ≤ e)
    (hweight : 0 ≤ weight)
    (hsf : ‖xsf‖ ≤ Csf * A * weight)
    (hR : ‖xR‖ ≤ Clf * g * weight)
    (hRp : ‖xRp‖ ≤ Clf * e * weight) :
    ‖xsf + xR + xRp‖
      ≤ shellConstant Csf Clf *
          shellActivity A g e * weight := by
  have hCsf_le : Csf ≤ shellConstant Csf Clf :=
    le_max_left _ _
  have hClf_le : Clf ≤ shellConstant Csf Clf :=
    le_max_right _ _
  have hsfb :
      Csf * A * weight
        ≤ shellConstant Csf Clf * A * weight := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCsf_le hA) hweight
  have hRb :
      Clf * g * weight
        ≤ shellConstant Csf Clf * g * weight := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hClf_le hg) hweight
  have hRpb :
      Clf * e * weight
        ≤ shellConstant Csf Clf * e * weight := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hClf_le he) hweight
  calc
    ‖xsf + xR + xRp‖
        ≤ ‖xsf + xR‖ + ‖xRp‖ :=
      norm_add_le _ _
    _ ≤ (‖xsf‖ + ‖xR‖) + ‖xRp‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (Csf * A * weight + Clf * g * weight) +
          Clf * e * weight := by
      gcongr
    _ ≤
      (shellConstant Csf Clf * A * weight +
        shellConstant Csf Clf * g * weight) +
        shellConstant Csf Clf * e * weight := by
      gcongr
    _ =
      shellConstant Csf Clf *
        shellActivity A g e * weight := by
      simp only [shellActivity]
      ring

theorem three_channel_bound_exp
    (xsf xR xRp : ℂ)
    (Csf Clf A g e mu d : ℝ)
    (hCsf : 0 ≤ Csf) (hClf : 0 ≤ Clf)
    (hA : 0 ≤ A) (hg : 0 ≤ g) (he : 0 ≤ e)
    (hsf : ‖xsf‖ ≤ Csf * A * Real.exp (-mu*d))
    (hR : ‖xR‖ ≤ Clf * g * Real.exp (-mu*d))
    (hRp : ‖xRp‖ ≤ Clf * e * Real.exp (-mu*d)) :
    ‖xsf + xR + xRp‖
      ≤ shellConstant Csf Clf *
          shellActivity A g e * Real.exp (-mu*d) := by
  exact three_channel_bound
    xsf xR xRp Csf Clf A g e (Real.exp (-mu*d))
    hCsf hClf hA hg he (Real.exp_pos _).le
    hsf hR hRp

#print axioms shellConstant_nonneg
#print axioms three_channel_bound
#print axioms three_channel_bound_exp

end YMUICV128.Section03.T009A
