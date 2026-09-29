import Mathlib

set_option autoImplicit false

/-!
# U2 source analyticity: explicit Frechet derivative and scalar source bounds
-/

namespace YMUICV128.Section03.T008B

noncomputable def rootFactor (W : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (W : ℂ)) - 1

noncomputable def clusterPhi
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) : ℂ :=
  C * (rootFactor Wp z.1 * rootFactor Wq z.2)

noncomputable def clusterPhiFDeriv
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) :
    (ℂ × ℂ) →L[ℂ] ℂ :=
  C •
    (rootFactor Wp z.1 •
        (Complex.exp (z.2 * (Wq : ℂ)) •
          ((Wq : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ))
      +
     rootFactor Wq z.2 •
        (Complex.exp (z.1 * (Wp : ℂ)) •
          ((Wp : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ)))

theorem clusterPhi_hasFDerivAt
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) :
    HasFDerivAt
      (fun y : ℂ × ℂ =>
        C * ((Complex.exp (y.1 * (Wp : ℂ)) - 1) *
          (Complex.exp (y.2 * (Wq : ℂ)) - 1)))
      (clusterPhiFDeriv C Wp Wq z) z := by
  have hs :
      HasFDerivAt
        (fun p : ℂ × ℂ => p.1 * (Wp : ℂ))
        ((Wp : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ) z :=
    hasFDerivAt_fst.mul_const (Wp : ℂ)
  have ht :
      HasFDerivAt
        (fun p : ℂ × ℂ => p.2 * (Wq : ℂ))
        ((Wq : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) z :=
    hasFDerivAt_snd.mul_const (Wq : ℂ)
  have ha := hs.cexp.sub_const (1 : ℂ)
  have hb := ht.cexp.sub_const (1 : ℂ)
  have hC := (ha.mul hb).const_mul C
  simpa only [rootFactor, Pi.mul_apply,
    clusterPhiFDeriv, smul_smul, smul_add,
    mul_comm, mul_left_comm, mul_assoc] using hC

theorem exp_real_mul_norm_le
    {W r : ℝ} {s : ℂ}
    (hr : 0 ≤ r) (hW0 : 0 ≤ W) (hW4 : W ≤ 4)
    (hs : ‖s‖ ≤ r) :
    ‖Complex.exp (s * (W : ℂ))‖ ≤ Real.exp (4*r) := by
  calc
    ‖Complex.exp (s * (W : ℂ))‖
        ≤ Real.exp ‖s * (W : ℂ)‖ :=
      Complex.norm_exp_le_exp_norm _
    _ ≤ Real.exp (4*r) := by
      apply Real.exp_le_exp.mpr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0]
      nlinarith [norm_nonneg s]

theorem rootFactor_norm_le
    {W r : ℝ} {s : ℂ}
    (hr : 0 ≤ r) (hW0 : 0 ≤ W) (hW4 : W ≤ 4)
    (hs : ‖s‖ ≤ r) :
    ‖rootFactor W s‖ ≤ Real.exp (4*r) + 1 := by
  unfold rootFactor
  calc
    ‖Complex.exp (s * (W : ℂ)) - 1‖
        ≤ ‖Complex.exp (s * (W : ℂ))‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ Real.exp (4*r) + 1 := by
      simpa using
        add_le_add_right
          (exp_real_mul_norm_le
            (W:=W) (r:=r) (s:=s) hr hW0 hW4 hs) 1

#print axioms clusterPhi_hasFDerivAt
#print axioms exp_real_mul_norm_le
#print axioms rootFactor_norm_le

end YMUICV128.Section03.T008B
