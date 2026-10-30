import YMOriginal.Original24_Taylor5FromU2Moment
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open Set

/-!
# C29 B10: the fifth moment is DERIVED from U2 exponential localization

For the ACTUAL finite-cutoff marked coefficients K_gamma and native
root-distance d_gamma>=0, assume precisely the established upstream U2
exponential weighted moment
  sum_gamma ||K_gamma|| exp(kappa*d_gamma) <= A.
No assumption on a polynomial fifth moment or on the Taylor remainder.

Using Real.pow_div_factorial_le_exp at degree five,
  d^5 <= 120*kappa^-5 exp(kappa*d),
the finite cutoff source Taylor remainder obeys
  ||Rem_4|| <= 5*A*M_f*kappa^-5 (a_j/a_n)^5.

The only further physical source input is the test-function fifth
directional derivative bound along the actual x->x+a_j*y line,
which comes from the original C^5 test assumption and the 4D
chain-rule/localization dictionary (not proved in this module).
-/

/-- Exact order-5 polynomial-to-exponential absorption with
the explicit factorial constant 5! = 120. -/
theorem fifth_power_absorbed_by_exp
    (kappa d : ℝ) (hk : 0 < kappa) (hd : 0 ≤ d) :
    d ^ 5 ≤ (120 / kappa ^ 5) * Real.exp (kappa * d) := by
  have hE : (kappa * d) ^ 5 / 120 ≤ Real.exp (kappa * d) := by
    simpa using Real.pow_div_factorial_le_exp
      (kappa * d) (mul_nonneg hk.le hd) 5
  have hk5 : 0 < kappa ^ 5 := pow_pos hk _
  have hpoly : kappa ^ 5 * d ^ 5 ≤
      120 * Real.exp (kappa * d) := by
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 120)).mp hE
    calc
      kappa ^ 5 * d ^ 5 = (kappa * d) ^ 5 := by ring
      _ ≤ Real.exp (kappa * d) * 120 := h
      _ = 120 * Real.exp (kappa * d) := by ring
  calc
    d ^ 5 ≤ (120 * Real.exp (kappa * d)) / (kappa ^ 5) :=
      (le_div_iff₀ hk5).mpr (by simpa only [mul_comm] using hpoly)
    _ = (120 / kappa ^ 5) * Real.exp (kappa * d) := by ring

/-- U2's uniform rooted exponential moment supplies the exact
fifth moment used in B10 for every finite polymer family. -/
theorem fifth_moment_from_U2_exponential
    {Γ : Type*} [Fintype Γ]
    (K : Γ → ℂ) (d : Γ → ℝ)
    (kappa A : ℝ)
    (hk : 0 < kappa)
    (hd : ∀ γ, 0 ≤ d γ)
    (hU2 : (∑ γ : Γ, ‖K γ‖ * Real.exp (kappa * d γ)) ≤ A) :
    (∑ γ : Γ, ‖K γ‖ * (d γ) ^ 5) ≤
      (120 / kappa ^ 5) * A := by
  have hC : 0 ≤ 120 / kappa ^ 5 :=
    div_nonneg (by norm_num) (pow_pos hk _).le
  calc
    (∑ γ : Γ, ‖K γ‖ * (d γ) ^ 5) ≤
      ∑ γ : Γ, (120 / kappa ^ 5) *
        (‖K γ‖ * Real.exp (kappa * d γ)) := by
      apply Finset.sum_le_sum
      intro γ hγ
      have h := fifth_power_absorbed_by_exp kappa (d γ) hk (hd γ)
      have hm := mul_le_mul_of_nonneg_left h (norm_nonneg (K γ))
      nlinarith
    _ = (120 / kappa ^ 5) *
        (∑ γ : Γ, ‖K γ‖ * Real.exp (kappa * d γ)) := by
      rw [Finset.mul_sum]
    _ ≤ (120 / kappa ^ 5) * A :=
      mul_le_mul_of_nonneg_left hU2 hC

/-- All fifth-order source/cluster moment assumptions are discharged
by U2's actual exponential moment. The output is the original
C29 B10 order-five decay, with an explicit constant. -/
theorem finite_B10_Taylor_from_U2_exponential
    {Γ : Type*} [Fintype Γ]
    (K : Γ → ℂ) (line : Γ → ℝ → ℂ)
    (d : Γ → ℝ)
    (aJ aN Mf kappa A : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN)
    (hMf : 0 ≤ Mf) (hk : 0 < kappa)
    (hd : ∀ γ, 0 ≤ d γ)
    (hf : ∀ γ, ContDiffOn ℝ 5 (line γ) (Icc 0 1))
    (hderiv : ∀ γ (t : ℝ), t ∈ Icc 0 1 →
      ‖iteratedDerivWithin 5 (line γ) (Icc 0 1) t‖ ≤
        Mf * (aJ / aN) ^ 5 * (d γ)^5)
    (hU2 : (∑ γ : Γ,
      ‖K γ‖ * Real.exp (kappa * d γ)) ≤ A) :
    ‖finiteMarkedTaylorRemainder K line‖ ≤
      (5 * A / kappa ^ 5) * Mf * (aJ / aN) ^ 5 := by
  have hmoment :=
    fifth_moment_from_U2_exponential K d kappa A hk hd hU2
  have hmain :=
    finite_marked_taylor_from_fifth_moment K line d
      aJ aN Mf ((120 / kappa ^ 5) * A)
      haJ haN hMf hd hf hderiv hmoment
  calc
    ‖finiteMarkedTaylorRemainder K line‖ ≤
      ((120 / kappa ^ 5) * A) * Mf * (aJ / aN) ^ 5 / 24 :=
      hmain
    _ = (5 * A / kappa ^ 5) * Mf * (aJ / aN) ^ 5 := by ring

end YMUIC.Original24
