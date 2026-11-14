import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.I7Cube

/-!
# Conditional physical-clock arithmetic for a Dobrushin--Shlosman cube

The mathematical reference has a one-step transfer gap at least
  -log(alpha)/(2*nCube)
from its genuine physical cube condition D(nCube,alpha).

For the original U--I--C manuscript terminal clock,
  nCube=2*nStar, aStar=nStar*a0, TStar=P^(2*nStar),
the elementary consequence is TStar|vac <= sqrt(alpha)*I.

This file proves only numerical exponent/mass-scale algebra.
It DOES NOT establish D(nCube,alpha) for Yang--Mills,
a physical transfer identity, or any form of model I7.
-/

/-- A cube of side 2*nStar with one-tick rate
-log(alpha)/(4*nStar) produces exactly sqrt(alpha)
after 2*nStar microscopic transfer steps. -/
theorem terminal_clock_exact_sqrt
    (alpha nStar : ℝ) (hAlpha : 0 < alpha) (hn : 0 < nStar) :
    Real.exp (-2*nStar*((-Real.log alpha)/(4*nStar))) =
      Real.sqrt alpha := by
  have hx :
      -2*nStar*((-Real.log alpha)/(4*nStar)) =
        Real.log alpha/2 := by
    field_simp [ne_of_gt hn]
    ring
  rw [hx]
  have he : (Real.exp (Real.log alpha / 2)) ^ 2 = alpha := by
    calc
      (Real.exp (Real.log alpha / 2)) ^ 2 =
          Real.exp (Real.log alpha / 2 + Real.log alpha / 2) := by
            rw [pow_two, Real.exp_add]
      _ = alpha := by
        rw [show Real.log alpha / 2 + Real.log alpha / 2 =
          Real.log alpha by ring, Real.exp_log hAlpha]
  have hr : (Real.sqrt alpha)^2 = alpha :=
    Real.sq_sqrt hAlpha.le
  have hp : 0 < Real.exp (Real.log alpha/2) := Real.exp_pos _
  have hsp : 0 ≤ Real.sqrt alpha := Real.sqrt_nonneg _
  nlinarith

/-- Pure arithmetic: a uniform one-tick cube gap at even side 2*nStar
forces a terminal-time contraction at most sqrt(alpha). -/
theorem uniform_terminal_bound_from_cube_gap
    (alpha nStar delta : ℝ)
    (hAlpha : 0 < alpha) (hAlpha1 : alpha < 1) (hn : 0 < nStar)
    (hGap : -Real.log alpha/(4*nStar) ≤ delta) :
    0 < 1 - Real.sqrt alpha ∧
      Real.exp (-2*nStar*delta) ≤ Real.sqrt alpha := by
  have hs : 0 ≤ Real.sqrt alpha := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt alpha)^2 = alpha := Real.sq_sqrt hAlpha.le
  have hs1 : Real.sqrt alpha < 1 := by nlinarith
  have hc : 0 ≤ 2*nStar := by positivity
  have hm := mul_le_mul_of_nonneg_left hGap hc
  have horder :
      -2*nStar*delta ≤ -2*nStar*((-Real.log alpha)/(4*nStar)) := by
    nlinarith only [hm]
  refine ⟨by linarith, ?_⟩
  calc
    Real.exp (-2*nStar*delta)
        ≤ Real.exp (-2*nStar*((-Real.log alpha)/(4*nStar))) :=
      Real.exp_le_exp.mpr horder
    _ = Real.sqrt alpha := terminal_clock_exact_sqrt alpha nStar hAlpha hn

#print axioms terminal_clock_exact_sqrt
#print axioms uniform_terminal_bound_from_cube_gap

end YMUIC.I7Cube
