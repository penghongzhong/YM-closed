import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.I7

/-!
# SU(2) Mandelstam fusion: exact 2 x 2 matrix backbone

This file proves a *matrix identity*, independent of physical coupling
and of I7. For determinant-one B, its adjugate is B^{-1}; hence the
algebraic result specializes to the SU(2) Wilson-loop Mandelstam identity.

No model spectral gap, transfer contraction, RG estimate, OS density
or Yang--Mills correlation decay is proved here.
-/

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Cayley-Hamilton's 2x2 trace fusion, written before the det(B)=1
specialization, for arbitrary complex matrices. -/
theorem trace_product_adjugate_fusion (A B : M2) :
    Matrix.trace A * Matrix.trace B =
      Matrix.trace (A * B) + Matrix.trace (A * B.adjugate) := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.adjugate_fin_two]
  ring

/-- Complex 2x2 Wilson root. For a determinant-one SU(2) holonomy,
trace is real and B.adjugate is the inverse B^{-1}. -/
def complexWilsonRoot (A : M2) : ℂ := 2 - Matrix.trace A

/-- An exact single-root fusion equation. When A and B are
SU(2) holonomies, the two terminal terms are the concatenated
loop and the concatenation with its reverse. -/
theorem complex_wilson_root_fusion (A B : M2) :
    complexWilsonRoot A * complexWilsonRoot B =
      2 * complexWilsonRoot A + 2 * complexWilsonRoot B -
        complexWilsonRoot (A * B) -
        complexWilsonRoot (A * B.adjugate) := by
  have h := trace_product_adjugate_fusion A B
  unfold complexWilsonRoot
  linear_combination h

#print axioms trace_product_adjugate_fusion
#print axioms complex_wilson_root_fusion

end YMUIC.I7
