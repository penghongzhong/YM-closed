import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

abbrev TestSpace4 := EuclideanSpace ℝ (Fin 4)

/-- The physical direction t↦t v as a genuine continuous linear map,
avoiding an artificial fifth-directional-derivative assumption. -/
def physicalLineCLM (v : TestSpace4) : ℝ →L[ℝ] TestSpace4 :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

theorem physical_line_clm_apply (v : TestSpace4) (t : ℝ) :
    physicalLineCLM v t = t • v := rfl

theorem physical_line_clm_norm (v : TestSpace4) :
    ‖physicalLineCLM v‖ = ‖v‖ := by
  unfold physicalLineCLM
  simpa using
    (ContinuousLinearMap.norm_smulRight_apply
      (ContinuousLinearMap.id ℝ ℝ) v)

/-- Actual Schwartz test-function evaluation along the 4D physical
RG source-to-root displacement. -/
def physicalTestLine (f : SchwartzMap TestSpace4 ℂ)
    (x v : TestSpace4) (t : ℝ) : ℂ :=
  f (x + physicalLineCLM v t)

/-- A genuine Schwartz source restricted to ANY physical affine line
is C^5; this property is DERIVED and not postulated for the source. -/
theorem physical_test_line_smooth
    (f : SchwartzMap TestSpace4 ℂ) (x v : TestSpace4) :
    ContDiff ℝ 5 (physicalTestLine f x v) := by
  have hShift : ContDiff ℝ 5
      (fun z : TestSpace4 => f (x + z)) :=
    (f.smooth 5).comp (contDiff_const.add contDiff_id)
  change ContDiff ℝ 5
    ((fun z : TestSpace4 => f (x + z)) ∘ physicalLineCLM v)
  exact hShift.comp (physicalLineCLM v).contDiff

/-- The 5th derivative of the physical test along an affine line is
controlled by the ACTUAL joint Schwartz 0,5 seminorm times ||v||^5.
No independent fifth derivative estimate is used. -/
theorem physical_test_line_fifth_norm
    (f : SchwartzMap TestSpace4 ℂ) (x v : TestSpace4)
    (t : ℝ) :
    ‖iteratedDeriv 5 (physicalTestLine f x v) t‖ ≤
      SchwartzMap.seminorm ℂ 0 5 f * ‖v‖ ^ 5 := by
  let g := physicalLineCLM v
  have hShift : ContDiff ℝ 5
      (fun z : TestSpace4 => f (x + z)) :=
    (f.smooth 5).comp (contDiff_const.add contDiff_id)
  have hComp :
      iteratedFDeriv ℝ 5 (physicalTestLine f x v) t =
        (iteratedFDeriv ℝ 5 f (x + g t)).compContinuousLinearMap
          (fun _ : Fin 5 => g) := by
    have hc := g.iteratedFDeriv_comp_right hShift t (le_refl 5)
    change iteratedFDeriv ℝ 5 (physicalTestLine f x v) t =
      (iteratedFDeriv ℝ 5
        (fun z : TestSpace4 => f (x + z)) (g t)).compContinuousLinearMap
        (fun _ : Fin 5 => g) at hc
    rw [hc]
    rw [iteratedFDeriv_comp_add_left (f := (f : TestSpace4 → ℂ)) 5 x (g t)]
  have hF : ‖iteratedFDeriv ℝ 5 f (x + g t)‖ ≤
      SchwartzMap.seminorm ℂ 0 5 f :=
    f.norm_iteratedFDeriv_le_seminorm 5 (x + g t)
  calc
    ‖iteratedDeriv 5 (physicalTestLine f x v) t‖ =
        ‖iteratedFDeriv ℝ 5 (physicalTestLine f x v) t‖ := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ = ‖(iteratedFDeriv ℝ 5 f (x + g t)).compContinuousLinearMap
          (fun _ : Fin 5 => g)‖ := by rw [hComp]
    _ ≤ ‖iteratedFDeriv ℝ 5 f (x + g t)‖ *
          (∏ _i : Fin 5, ‖g‖) :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ 5 f (x + g t)‖ * ‖g‖ ^ 5 := by simp
    _ ≤ SchwartzMap.seminorm ℂ 0 5 f * ‖g‖ ^ 5 :=
        mul_le_mul_of_nonneg_right hF (pow_nonneg (norm_nonneg _) _)
    _ = SchwartzMap.seminorm ℂ 0 5 f * ‖v‖ ^ 5 := by
        rw [physical_line_clm_norm]

/-- Within [0,1] the physical line's 5th derivative is identical to
the global 5th derivative and has the same genuine Schwartz bound. -/
theorem physical_test_line_within_fifth_norm
    (f : SchwartzMap TestSpace4 ℂ) (x v : TestSpace4)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖iteratedDerivWithin 5 (physicalTestLine f x v) (Set.Icc 0 1) t‖ ≤
      SchwartzMap.seminorm ℂ 0 5 f * ‖v‖ ^ 5 := by
  have hd : ContDiffAt ℝ 5 (physicalTestLine f x v) t :=
    (physical_test_line_smooth f x v).contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)) hd ht]
  exact physical_test_line_fifth_norm f x v t

end YMUIC.Original24
