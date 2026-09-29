import Mathlib

set_option autoImplicit false

/-!
# U2 marked-shell theorem: one-variable Cauchy derivative certificate

This certificate isolates the exact Cauchy estimate used after fixing one
source variable.  It does not encode the paper's two-variable identification;
that is assembled in T009C.
-/

namespace YMUICV128.Section03.T009B

open Complex Metric

theorem cauchy_first_deriv_bound
    {f : ℂ → ℂ} {r C : ℝ}
    (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball 0 r))
    (hC : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ C) :
    ‖deriv f 0‖ ≤ C / r := by
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr hf hC

theorem cauchy_second_deriv_bound
    {f : ℂ → ℂ} {r C : ℝ}
    (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball 0 r))
    (hC : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ C) :
    ‖iteratedDeriv 2 f 0‖ ≤ 2 * C / r ^ 2 := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (F := ℂ) 2 hr hf hC
  norm_num at h ⊢
  exact h

#print axioms cauchy_first_deriv_bound
#print axioms cauchy_second_deriv_bound

end YMUICV128.Section03.T009B
