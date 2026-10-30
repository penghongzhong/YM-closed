import YMOriginal.Original24_PhysicalSchwartzLine
import YMOriginal.Original24_TaylorU1U2Marked

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Actual 4D Schwartz C^5 B10 for a finite SU2 Wilson root

The test function is the genuine physical f∈S(R⁴), sampled along
  f(x_gamma + t*a_j*y_gamma), 0<=t<=1.
C^5 differentiability and the norm of its FIFTH directional derivative
are DERIVED from the actual Schwartz 0,5 seminorm and linear restriction,
NOT introduced as test-function derivative hypotheses.

From U1 genuine unmarked activity, U2 exponential rooted tree count,
this proves the true 4th-order marked Taylor remainder:
  ||Rem_4|| <= Croot*(a_j/a_n)^5,
with explicit coefficient from the same fixed Wilson word polynomial.
The upstream hU2tree remains the model's rooted count; the subsequent
physical source/RG jet matching is not yet supplied by this theorem.
-/

/-- Schwartz f and physical source positions/displacements determine
the actual 1D Taylor test lines, no artificial line function. -/
def actualSchwartzTaylorLine
    {Γ : Type*} (f : SchwartzMap TestSpace4 ℂ)
    (position displacement : Γ → TestSpace4)
    (aJ : ℝ) (γ : Γ) : ℝ → ℂ :=
  physicalTestLine f (position γ) (aJ • displacement γ)

/-- A genuine 4D Schwartz fifth derivative bound produces the exact
rescaled C29 B10 input on every physical Taylor line, with no
postulated fifth-derivative estimate. -/
theorem actual_schwartz_directional_fifth_bound
    {Γ : Type*}
    (f : SchwartzMap TestSpace4 ℂ)
    (position displacement : Γ → TestSpace4)
    (aJ aN Mf : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN)
    (hTest : SchwartzMap.seminorm ℂ 0 5 f ≤ Mf / aN ^ 5) :
    ∀ γ (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      ‖iteratedDerivWithin 5
        (actualSchwartzTaylorLine f position displacement aJ γ)
        (Set.Icc 0 1) t‖ ≤
        Mf * (aJ / aN) ^ 5 * ‖displacement γ‖ ^ 5 := by
  intro γ t ht
  have hnV : ‖aJ • displacement γ‖ = aJ * ‖displacement γ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg haJ]
  have hActual :=
    physical_test_line_within_fifth_norm f
      (position γ) (aJ • displacement γ) t ht
  have hscale : 0 ≤ (aJ * ‖displacement γ‖) ^ 5 := by positivity
  calc
    ‖iteratedDerivWithin 5
      (actualSchwartzTaylorLine f position displacement aJ γ)
      (Set.Icc 0 1) t‖ ≤
        SchwartzMap.seminorm ℂ 0 5 f * ‖aJ • displacement γ‖ ^ 5 :=
          hActual
    _ = SchwartzMap.seminorm ℂ 0 5 f *
        (aJ * ‖displacement γ‖) ^ 5 := by rw [hnV]
    _ ≤ (Mf / aN ^ 5) * (aJ * ‖displacement γ‖) ^ 5 :=
      mul_le_mul_of_nonneg_right hTest hscale
    _ = Mf * (aJ / aN) ^ 5 * ‖displacement γ‖ ^ 5 := by
      field_simp [haN.ne']
      ring

/-- Actual finite-cutoff marked external Wilson-word source B10
fifth-order Taylor conclusion, from U1 unmarked exponential
localization, U2 rooted count and an ACTUAL Schwartz seminorm.

This theorem has no independently postulated hB10 or hline5.
All required finite-data sources are genuine SU2 holonomy words.
-/
theorem actual_schwartz_B10_from_U1_U2
    {P T Γ : Type*} [Fintype T] [Fintype Γ]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ) (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (unmarked : Γ → ℂ)
    (position displacement : Γ → TestSpace4)
    (kappa mu A Ctree : ℝ)
    (hA : 0 ≤ A) (hmu : 0 < mu)
    (hunmarked : ∀ γ,
      ‖unmarked γ‖ ≤ A * Real.exp (-kappa * ‖displacement γ‖))
    (hU2tree : (∑ γ : Γ,
      Real.exp (-(kappa - mu) * ‖displacement γ‖)) ≤ Ctree)
    (f : SchwartzMap TestSpace4 ℂ)
    (aJ aN Mf : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN) (hMf : 0 ≤ Mf)
    (hTest : SchwartzMap.seminorm ℂ 0 5 f ≤ Mf / aN ^ 5) :
    ‖finiteMarkedTaylorRemainder
      (actualWordMarkedR U words coeff s unmarked)
      (actualSchwartzTaylorLine f position displacement aJ)‖ ≤
      (5 * ((2 * ‖s‖ * actualWilsonPolynomialBudget words coeff * A) *
        Ctree) / mu ^ 5) * Mf * (aJ / aN) ^ 5 := by
  exact actual_U1_U2_fifth_Taylor_source
    U words coeff s hsmall unmarked
    (fun γ => ‖displacement γ‖)
    kappa mu A Ctree hA hmu (fun γ => norm_nonneg _) hunmarked
    hU2tree
    (actualSchwartzTaylorLine f position displacement aJ)
    aJ aN Mf haJ haN hMf
    (fun γ =>
      (physical_test_line_smooth f (position γ)
        (aJ • displacement γ)).contDiffOn)
    (actual_schwartz_directional_fifth_bound
      f position displacement aJ aN Mf haJ haN hTest)

end YMUIC.Original24
