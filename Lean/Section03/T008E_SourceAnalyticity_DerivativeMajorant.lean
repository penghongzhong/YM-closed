import Mathlib

set_option autoImplicit false

/-!
# U2 source analyticity: explicit derivative majorant

On |s|,|t| <= r and 0 <= Wp,Wq <= 4,
  ||D Phi_C(s,t)|| <= K'_r ||C||,
  K'_r = 8 exp(4r) (exp(4r)+1).
-/

namespace YMUICV128.Section03.T008E

noncomputable def rootFactor (W : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (W : ℂ)) - 1

noncomputable def derivMap
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) :
    (ℂ × ℂ) →L[ℂ] ℂ :=
  (C * rootFactor Wq z.2 *
      Complex.exp (z.1 * (Wp : ℂ)) * (Wp : ℂ))
      • ContinuousLinearMap.fst ℂ ℂ ℂ
  +
  (C * rootFactor Wp z.1 *
      Complex.exp (z.2 * (Wq : ℂ)) * (Wq : ℂ))
      • ContinuousLinearMap.snd ℂ ℂ ℂ

noncomputable def derivConstant (r : ℝ) : ℝ :=
  8 * Real.exp (4*r) * (Real.exp (4*r) + 1)

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

theorem derivMap_norm_le
    {C : ℂ} {Wp Wq r : ℝ} {z : ℂ × ℂ}
    (hr : 0 ≤ r)
    (hWp0 : 0 ≤ Wp) (hWp4 : Wp ≤ 4)
    (hWq0 : 0 ≤ Wq) (hWq4 : Wq ≤ 4)
    (hs : ‖z.1‖ ≤ r) (ht : ‖z.2‖ ≤ r) :
    ‖derivMap C Wp Wq z‖
      ≤ derivConstant r * ‖C‖ := by
  let E : ℝ := Real.exp (4*r)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hRp : ‖rootFactor Wp z.1‖ ≤ E + 1 := by
    exact rootFactor_norm_le
      (r:=r) (W:=Wp) (s:=z.1) hr hWp0 hWp4 hs
  have hRq : ‖rootFactor Wq z.2‖ ≤ E + 1 := by
    exact rootFactor_norm_le
      (r:=r) (W:=Wq) (s:=z.2) hr hWq0 hWq4 ht
  have hEs : ‖Complex.exp (z.1 * (Wp : ℂ))‖ ≤ E := by
    exact exp_real_mul_norm_le
      (r:=r) (W:=Wp) (s:=z.1) hr hWp0 hWp4 hs
  have hEt : ‖Complex.exp (z.2 * (Wq : ℂ))‖ ≤ E := by
    exact exp_real_mul_norm_le
      (r:=r) (W:=Wq) (s:=z.2) hr hWq0 hWq4 ht
  have hNp : ‖(Wp : ℂ)‖ ≤ 4 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWp0] using hWp4
  have hNq : ‖(Wq : ℂ)‖ ≤ 4 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWq0] using hWq4
  let A : ℂ :=
    C * rootFactor Wq z.2 *
      Complex.exp (z.1 * (Wp : ℂ)) * (Wp : ℂ)
  let B : ℂ :=
    C * rootFactor Wp z.1 *
      Complex.exp (z.2 * (Wq : ℂ)) * (Wq : ℂ)
  have hA :
      ‖A‖ ≤ ‖C‖ * (E + 1) * E * 4 := by
    dsimp [A]
    simp only [norm_mul]
    gcongr
  have hB :
      ‖B‖ ≤ ‖C‖ * (E + 1) * E * 4 := by
    dsimp [B]
    simp only [norm_mul]
    gcongr
  calc
    ‖derivMap C Wp Wq z‖
        = ‖A • ContinuousLinearMap.fst ℂ ℂ ℂ
            + B • ContinuousLinearMap.snd ℂ ℂ ℂ‖ := by
          rfl
    _ ≤ ‖A • ContinuousLinearMap.fst ℂ ℂ ℂ‖
          + ‖B • ContinuousLinearMap.snd ℂ ℂ ℂ‖ :=
      norm_add_le _ _
    _ = ‖A‖ + ‖B‖ := by
      simp [norm_smul]
    _ ≤ (‖C‖ * (E + 1) * E * 4)
          + (‖C‖ * (E + 1) * E * 4) :=
      add_le_add hA hB
    _ = derivConstant r * ‖C‖ := by
      dsimp [derivConstant, E]
      ring

theorem derivMap_norm_le_treeWeight
    {C : ℂ} {Wp Wq r treeWeight : ℝ} {z : ℂ × ℂ}
    (hr : 0 ≤ r)
    (hWp0 : 0 ≤ Wp) (hWp4 : Wp ≤ 4)
    (hWq0 : 0 ≤ Wq) (hWq4 : Wq ≤ 4)
    (hs : ‖z.1‖ ≤ r) (ht : ‖z.2‖ ≤ r)
    (htree0 : 0 ≤ treeWeight)
    (hC : ‖C‖ ≤ treeWeight) :
    ‖derivMap C Wp Wq z‖
      ≤ derivConstant r * treeWeight := by
  exact (derivMap_norm_le hr hWp0 hWp4 hWq0 hWq4 hs ht).trans
    (mul_le_mul_of_nonneg_left hC (by
      unfold derivConstant
      positivity))

#print axioms derivMap_norm_le
#print axioms derivMap_norm_le_treeWeight

end YMUICV128.Section03.T008E
