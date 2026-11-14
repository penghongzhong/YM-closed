import YMOriginal.OriginalI7_MandelstamSU2
import YM.Wilson.RootBound

set_option autoImplicit false
noncomputable section

namespace YMUIC.I7
open YMUICV128.Section03

/-!
# Mandelstam fusion for the ACTUAL real-valued Wilson root

The preceding strict Lean gate proved the group-level complex trace
identity. This module identifies the fundamental SU(2) trace with a
real number and specializes to the repository's exact definition
wilsonRoot U = 2 - (trace U).re.

No physical covariance or mass-gap estimate is claimed.
-/

/-- The fundamental SU(2) trace is real. -/
theorem su2_trace_im_zero (U : SU2) :
    (Matrix.trace (U : M2)).im = 0 := by
  have hInv : Matrix.trace ((U⁻¹ : SU2) : M2) =
      Matrix.trace (U : M2) := by
    rw [su2_matrix_inverse_eq_adjugate U]
    simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two]
    ring
  have hStar : Matrix.trace ((U⁻¹ : SU2) : M2) =
      star (Matrix.trace (U : M2)) := by
    change Matrix.trace (star (U : M2)) =
      star (Matrix.trace (U : M2))
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.trace_conjTranspose (U : M2)
  have hStarFix : star (Matrix.trace (U : M2)) =
      Matrix.trace (U : M2) := hStar.symm.trans hInv
  have hIm := congrArg Complex.im hStarFix
  simp only [Complex.star_def, Complex.conj_im] at hIm
  linarith

/-- Actual repository Wilson root fusion; no complex-root substitution.
For two closed SU(2) holonomies, both right-hand products are again
closed holonomies at the common basepoint. -/
theorem su2_actual_wilson_root_fusion (A B : SU2) :
    wilsonRoot A * wilsonRoot B =
      2 * wilsonRoot A + 2 * wilsonRoot B -
      wilsonRoot (A * B) - wilsonRoot (A * B⁻¹) := by
  have h := congrArg Complex.re (su2_mandelstam_trace A B)
  simp [Complex.mul_re, su2_trace_im_zero A, su2_trace_im_zero B] at h
  unfold wilsonRoot
  linear_combination h

#print axioms su2_trace_im_zero
#print axioms su2_actual_wilson_root_fusion

end YMUIC.I7
