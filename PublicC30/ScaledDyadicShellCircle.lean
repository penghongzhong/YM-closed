import PublicC30.ScaledDyadicShellMargin
import YM.OSGrowth.DyadicShellRegularity
import Mathlib.Topology.Instances.AddCircle.Defs

set_option autoImplicit false
namespace YMUIC.OSTensor

open YMUIC.OSGrowth

/-- The original dyadic shell normalized to one real physical coordinate.
This is the actual `dyadicShell`, not an abstract substitute. -/
noncomputable def scaledDyadicShellReal (n : ℕ) : ℝ → ℝ :=
  fun x => dyadicShell (E := ℝ) (n + 1) ((2 : ℝ) ^ (n + 4) • x)

theorem scaled_dyadic_shell_real_continuous (n : ℕ) :
    Continuous (scaledDyadicShellReal n) := by
  have hc := ((dyadic_shell_regularity (E := ℝ) (n + 1)).1).continuous
  have hs : Continuous (fun x : ℝ => ((2 : ℝ) ^ (n + 4)) • x) := by
    fun_prop
  exact hc.comp hs

/-- Both endpoints of the chosen fundamental interval are zeros of the actual
rescaled shell; the periodicization therefore has no value jump at the seam. -/
theorem scaled_dyadic_shell_real_seam (n : ℕ) :
    scaledDyadicShellReal n (-1 / 2) = 0 ∧
    scaledDyadicShellReal n (1 / 2) = 0 := by
  constructor
  · exact scaled_dyadic_shell_outer_margin (E := ℝ) n (-1 / 2 : ℝ)
      (by norm_num [Real.norm_eq_abs, abs_neg])
  · exact scaled_dyadic_shell_outer_margin (E := ℝ) n (1 / 2 : ℝ)
      (by norm_num [Real.norm_eq_abs])

/-- A concrete, continuous periodization of a non-initial dyadic shell on
`ℝ/ℤ`, obtained by gluing a fundamental interval with matching endpoints. -/
noncomputable def scaledDyadicShellUnitCircle (n : ℕ) :
    C(UnitAddCircle, ℝ) := by
  have hseam :
      scaledDyadicShellReal n (-1 / 2) =
        scaledDyadicShellReal n ((-1 / 2 : ℝ) + 1) := by
    have h := scaled_dyadic_shell_real_seam n
    simpa only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      using h.1.trans h.2.symm
  exact ⟨AddCircle.liftIco (1 : ℝ) (-1 / 2 : ℝ) (scaledDyadicShellReal n),
    AddCircle.liftIco_continuous (p := (1 : ℝ)) (a := (-1 / 2 : ℝ))
      hseam (scaled_dyadic_shell_real_continuous n).continuousOn⟩

/-- On the original interior cell, the periodicized value is exactly the
rescaled Wilson-relevant dyadic shell value. -/
theorem scaled_dyadic_shell_unit_circle_apply
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Ico (-1 / 2 : ℝ) (1 / 2)) :
    scaledDyadicShellUnitCircle n (x : UnitAddCircle) = scaledDyadicShellReal n x := by
  change AddCircle.liftIco (1 : ℝ) (-1 / 2 : ℝ)
    (scaledDyadicShellReal n) (x : UnitAddCircle) = _
  exact AddCircle.liftIco_coe_apply
    (p := (1 : ℝ)) (a := (-1 / 2 : ℝ)) (f := scaledDyadicShellReal n)
    (by simpa only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using hx)

end YMUIC.OSTensor
