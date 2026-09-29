import Mathlib

set_option autoImplicit false

/-!
# U2 marked-shell theorem: Cauchy extraction assembly

This certificate isolates the final analytic implication used by the paper:
a uniform bidisc bound for a jointly holomorphic shell generating function
gives the mixed derivative / covariance bound by two applications of the
one-variable Cauchy estimate.
-/

namespace YMUICV128.Section03.T009B

theorem mixed_deriv_cauchy_bound
    (K : ℂ × ℂ → ℂ)
    (r M : ℝ)
    (hr : 0 < r)
    (hK : Differentiable ℂ K)
    (hM :
      ∀ s t : ℂ, ‖s‖ ≤ r → ‖t‖ ≤ r →
        ‖K (s,t)‖ ≤ M) :
    ‖fderiv ℂ (fun s : ℂ => fderiv ℂ (fun t : ℂ => K (s,t)) 0 1) 0 1‖
      ≤ r⁻¹ * (r⁻¹ * M) := by
  have hslice_t :
      ∀ s : ℂ, Differentiable ℂ (fun t : ℂ => K (s,t)) := by
    intro s
    exact hK.comp (differentiable_const.prod differentiable_id)
  have hinner :
      ∀ s : ℂ, ‖s‖ ≤ r →
        ‖fderiv ℂ (fun t : ℂ => K (s,t)) 0 1‖
          ≤ r⁻¹ * M := by
    intro s hs
    have hdiff := hslice_t s
    exact norm_fderiv_apply_le_of_eq_zero
      hr hdiff.differentiableAt
      (fun z hz => hM s z hs (le_of_lt hz))
  have hs_fun :
      Differentiable ℂ
        (fun s : ℂ => fderiv ℂ (fun t : ℂ => K (s,t)) 0 1) := by
    fun_prop
  exact norm_fderiv_apply_le_of_eq_zero
    hr hs_fun.differentiableAt
    (fun z hz => hinner z (le_of_lt hz))

theorem covariance_bound_from_shell
    (cov : ℂ)
    (r C alpha weight : ℝ)
    (hr : 0 < r)
    (hC : 0 ≤ C) (ha : 0 ≤ alpha) (hw : 0 ≤ weight)
    (hcov :
      ‖cov‖ ≤ r⁻¹ * (r⁻¹ * (C * alpha * weight))) :
    ‖cov‖ ≤ r⁻² * C * alpha * weight := by
  calc
    ‖cov‖ ≤ r⁻¹ * (r⁻¹ * (C * alpha * weight)) := hcov
    _ = r⁻² * C * alpha * weight := by
      field_simp [ne_of_gt hr]
      ring

#print axioms mixed_deriv_cauchy_bound
#print axioms covariance_bound_from_shell

end YMUICV128.Section03.T009B
