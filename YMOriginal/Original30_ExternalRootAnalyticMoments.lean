import YMOriginal.Original30_LocalSourceShellBudget
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open Metric Set

/-!
# Bounded external roots produce the uniform analytic source budget

This is the v124R -> v120 bridge in its minimal form.  The bulk activity is
not source-deformed.  A fixed-complexity external root enters only through a
bounded continuous linear source functional L_gamma.  The resulting marked
activity z_gamma (exp(L_gamma J)-1) is entire and inherits the unmarked
exponential polymer localization.  Hence the existing shell-count theorem
produces the all-order factorial source-moment bound.
-/

def boundedExternalRootActivity
    {E Γ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z : Γ → ℂ) (L : Γ → E →L[ℂ] ℂ) (γ : Γ) (J : E) : ℂ :=
  z γ * (Complex.exp (L γ J) - 1)

/-- A bounded external root preserves the unmarked exponential polymer
envelope on a fixed source ball.  No post-R arbitrary-source analyticity is
assumed. -/
theorem bounded_external_root_activity_bound
    {E Γ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z : Γ → ℂ) (L : Γ → E →L[ℂ] ℂ)
    (length : Γ → ℕ)
    (A B kappa rho : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hrho : 0 < rho)
    (hz : ∀ γ, ‖z γ‖ ≤ A * Real.exp (-kappa * (length γ : ℝ)))
    (hL : ∀ γ, ‖L γ‖ ≤ B) :
    ∀ γ J, J ∈ ball (0 : E) rho →
      ‖boundedExternalRootActivity z L γ J‖ ≤
        (A * (Real.exp (B * rho) + 1)) *
          Real.exp (-kappa * (length γ : ℝ)) := by
  intro γ J hJ
  have hJnorm : ‖J‖ ≤ rho := by
    have hlt : ‖J‖ < rho := by
      simpa [mem_ball, dist_zero_right] using hJ
    exact hlt.le
  have hLJ : ‖L γ J‖ ≤ B * rho := by
    calc
      ‖L γ J‖ ≤ ‖L γ‖ * ‖J‖ := (L γ).le_opNorm J
      _ ≤ B * rho :=
        mul_le_mul (hL γ) hJnorm (norm_nonneg _) hB
  have hexp : ‖Complex.exp (L γ J)‖ ≤ Real.exp (B * rho) := by
    calc
      ‖Complex.exp (L γ J)‖ ≤ Real.exp ‖L γ J‖ :=
        Complex.norm_exp_le_exp_norm _
      _ ≤ Real.exp (B * rho) := Real.exp_le_exp.mpr hLJ
  have hmark : ‖Complex.exp (L γ J) - 1‖ ≤ Real.exp (B * rho) + 1 := by
    calc
      _ ≤ ‖Complex.exp (L γ J)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp (B * rho) + 1 := by simpa using add_le_add_right hexp 1
  simp only [boundedExternalRootActivity, norm_mul]
  calc
    ‖z γ‖ * ‖Complex.exp (L γ J) - 1‖ ≤
        (A * Real.exp (-kappa * (length γ : ℝ))) *
          (Real.exp (B * rho) + 1) :=
      mul_le_mul (hz γ) hmark (norm_nonneg _)
        (mul_nonneg hA (Real.exp_pos _).le)
    _ = (A * (Real.exp (B * rho) + 1)) *
          Real.exp (-kappa * (length γ : ℝ)) := by ring

theorem bounded_external_root_activity_analytic
    {E Γ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z : Γ → ℂ) (L : Γ → E →L[ℂ] ℂ) (γ : Γ) (rho : ℝ) :
    AnalyticOnNhd ℂ (boundedExternalRootActivity z L γ) (ball (0 : E) rho) := by
  intro J hJ
  exact analyticAt_const.mul (((L γ).analyticAt J).cexp.sub analyticAt_const)

/-- Main v124R/v120 bridge.  Exponentially localized unmarked polymer
activities plus bounded external roots and the native shell count yield a
cutoff-independent normalized generating function with single-factorial
all-order derivatives. -/
theorem bounded_external_roots_to_factorial_source_moments
    {E Γ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Γ]
    (z : Γ → ℂ) (L : Γ → E →L[ℂ] ℂ)
    (length : Γ → ℕ)
    (A B C kappa sigma rho : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrho : 0 < rho) (hgap : sigma < kappa)
    (hz : ∀ γ, ‖z γ‖ ≤ A * Real.exp (-kappa * (length γ : ℝ)))
    (hL : ∀ γ, ‖L γ‖ ≤ B)
    (hcount : ∀ m : ℕ,
      ((((Finset.univ : Finset Γ).filter (fun γ => length γ = m)).card : ℝ)) ≤
        C * Real.exp (sigma * (m : ℝ))) :
    let epsilon := A * (Real.exp (B * rho) + 1)
    let Z : E → ℂ := fun J =>
      Complex.exp
        ((∑ γ : Γ, boundedExternalRootActivity z L γ J) -
          ∑ γ : Γ, boundedExternalRootActivity z L γ 0)
    AnalyticOnNhd ℂ Z (ball 0 rho) ∧ Z 0 = 1 ∧
      ∀ (r : ℕ) (h : Fin r → E),
        ‖iteratedFDeriv ℂ r Z 0 h‖ ≤
          Real.exp 1 * (r.factorial : ℝ) *
            (Real.exp 1 *
              (1 + 2 * (epsilon * C /
                (1 - Real.exp (-(kappa - sigma))))) / rho) ^ r *
            ∏ j, ‖h j‖ := by
  dsimp
  let epsilon : ℝ := A * (Real.exp (B * rho) + 1)
  have heps : 0 ≤ epsilon := by
    dsimp [epsilon]
    positivity
  have hlocal :
      ∀ i ∈ (Finset.univ : Finset Γ), ¬ (fun _ : Γ => True) i →
        ∀ J ∈ ball (0 : E) rho,
          boundedExternalRootActivity z L i J =
            boundedExternalRootActivity z L i 0 := by
    intro i hi hfalse
    exact False.elim (hfalse trivial)
  have hanalytic :
      ∀ i ∈ (Finset.univ : Finset Γ).filter (fun _ : Γ => True),
        AnalyticOnNhd ℂ (boundedExternalRootActivity z L i) (ball (0 : E) rho) := by
    intro i hi
    exact bounded_external_root_activity_analytic z L i rho
  have hweight :
      ∀ i ∈ (Finset.univ : Finset Γ).filter (fun _ : Γ => True),
        ∀ J ∈ ball (0 : E) rho,
          ‖boundedExternalRootActivity z L i J‖ ≤
            epsilon * Real.exp (-kappa * (length i : ℝ)) := by
    intro i hi J hJ
    exact bounded_external_root_activity_bound
      z L length A B kappa rho hA hB hrho hz hL i J hJ
  have hc :
      ∀ m : ℕ,
        (((((Finset.univ : Finset Γ).filter (fun _ : Γ => True)).filter
          (fun i => length i = m)).card : ℝ)) ≤
          C * Real.exp (sigma * (m : ℝ)) := by
    intro m
    simpa using hcount m
  simpa [epsilon] using
    (local_source_moments_from_shell_count
      (Γ := (Finset.univ : Finset Γ))
      (active := fun _ : Γ => True)
      (activity := boundedExternalRootActivity z L)
      (length := length)
      epsilon C kappa sigma rho hrho heps hC hgap
      hlocal hanalytic hweight hc)

#print axioms bounded_external_roots_to_factorial_source_moments

end YMUIC.Original30
