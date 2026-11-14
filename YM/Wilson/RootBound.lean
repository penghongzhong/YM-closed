import Mathlib

set_option autoImplicit false

/-!
# v133 U2: Wilson plaquette root bound

This certifies the first internal claim in U2:
  W_p(U) = 2 - Re Tr(U_p),
  0 ≤ W_p(U) ≤ 4
for U_p ∈ SU(2).

Only unitarity is needed for this bound; det(U_p)=1 is not used.
-/

namespace YMUICV128.Section03

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

def wilsonRoot (U : SU2) : ℝ :=
  2 - (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re

theorem diagonal_re_bounds (U : SU2) (i : Fin 2) :
    -1 ≤ ((U : Matrix (Fin 2) (Fin 2) ℂ) i i).re
      ∧ ((U : Matrix (Fin 2) (Fin 2) ℂ) i i).re ≤ 1 := by
  have hunit :
      (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup U.property
  have hentry :
      ‖(U : Matrix (Fin 2) (Fin 2) ℂ) i i‖ ≤ 1 :=
    entry_norm_bound_of_unitary hunit i i
  have hre :
      |((U : Matrix (Fin 2) (Fin 2) ℂ) i i).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans hentry
  exact abs_le.mp hre

theorem trace_re_bounds (U : SU2) :
    -2 ≤ (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re
      ∧ (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re ≤ 2 := by
  rcases diagonal_re_bounds U 0 with ⟨h00l, h00u⟩
  rcases diagonal_re_bounds U 1 with ⟨h11l, h11u⟩
  simp only [Matrix.trace_fin_two, Complex.add_re]
  constructor <;> linarith

theorem wilsonRoot_bounds (U : SU2) :
    0 ≤ wilsonRoot U ∧ wilsonRoot U ≤ 4 := by
  rcases trace_re_bounds U with ⟨hl, hu⟩
  unfold wilsonRoot
  constructor <;> linarith

#print axioms diagonal_re_bounds
#print axioms trace_re_bounds
#print axioms wilsonRoot_bounds

end YMUICV128.Section03
