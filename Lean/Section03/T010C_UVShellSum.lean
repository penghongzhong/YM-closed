import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010C

theorem uv_shell_sum_bound
    (S T Cstar mu Binf : ℝ)
    (hfac : 0 ≤ Cstar * Real.exp (mu * Binf))
    (hST : S ≤ T) :
    Cstar * Real.exp (mu * Binf) * S
      ≤ Cstar * Real.exp (mu * Binf) * T := by
  exact mul_le_mul_of_nonneg_left hST hfac

#print axioms uv_shell_sum_bound

end YMUICV128.Section03.T010C
