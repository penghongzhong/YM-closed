import YMConditional.Original15_OperatorOrder
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.ConditionalI7
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The usual resolvent definition for a genuinely partially defined operator.
The inverse must be a bounded operator on the entire Hilbert space, take values
in the generator domain, and be both a left and a right inverse. -/
def generatorResolvent (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ (R : H →L[ℂ] H) (hR : ∀ x : H, R x ∈ A.domain),
    (∀ x : H, A ⟨R x, hR x⟩ - z • R x = x) ∧
    (∀ x : A.domain, R (A x - z • (x : H)) = (x : H))}

/-- Full resolvent-complement spectrum, not the point spectrum. -/
def generatorSpectrum (A : H →ₗ.[ℂ] H) : Set ℂ := (generatorResolvent A)ᶜ

/-- Explicit standard external spectral-theorem interface.
For a nonnegative self-adjoint generator A and T=exp(-t A), the spectral
calculus supplies these two facts. The interface contains NO spectral gap,
no upper bound on T, no I7 assumption and no spectral lower bound on A.
This file does not claim to prove the unbounded spectral theorem itself. -/
structure HeatSpectralInput (A : H →ₗ.[ℂ] H) (t : ℝ) (T : H →L[ℂ] H) : Prop where
  real_spectrum : ∀ z ∈ generatorSpectrum A, z.im = 0
  heat_spectral_inclusion : ∀ E : ℝ, (E : ℂ) ∈ generatorSpectrum A →
    (Real.exp (-t * E) : ℂ) ∈ spectrum ℂ T

/-- A real number above a quadratic-form upper bound is in the resolvent.
This uses bounded inverse existence, hence excludes continuous spectrum too. -/
theorem transfer_resolvent_above_bound
    (T : H →L[ℂ] H) (q s : ℝ)
    (hform : ∀ x : H, (⟪T x, x⟫_ℂ).re ≤ q * ‖x‖ ^ 2)
    (hqs : q < s) : (s : ℂ) ∉ spectrum ℂ T := by
  apply spectrum.notMem_iff.mpr
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (c := ⟨s - q, sub_nonneg.mpr hqs.le⟩)
  · exact_mod_cast sub_pos.mpr hqs
  · intro x
    have h := hform x
    have hre :
        (s - q) * ‖x‖ ^ 2 ≤
          (⟪(algebraMap ℂ (H →L[ℂ] H) (s : ℂ) - T) x, x⟫_ℂ).re := by
      simp only [Algebra.algebraMap_eq_smul_one, sub_apply,
        smul_apply, one_apply_eq_self,
        inner_sub_left, inner_smul_left, Complex.sub_re,
        Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      have hn : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
      rw [hn]
      nlinarith
    have hnorm := hre.trans (Complex.re_le_norm _)
    change ‖x‖ ^ 2 * (s - q) ≤
      ‖⟪(algebraMap ℂ (H →L[ℂ] H) (s : ℂ) - T) x, x⟫_ℂ‖
    simpa only [mul_comm] using hnorm

/-- The whole real transfer spectrum obeys the quadratic-form upper bound. -/
theorem transfer_spectrum_le
    (T : H →L[ℂ] H) (q s : ℝ)
    (hform : ∀ x : H, (⟪T x, x⟫_ℂ).re ≤ q * ‖x‖ ^ 2)
    (hs : (s : ℂ) ∈ spectrum ℂ T) : s ≤ q := by
  by_contra h
  exact transfer_resolvent_above_bound T q s hform (lt_of_not_ge h) hs

/-- Elementary exact logarithmic threshold; no eigenvalue assumption. -/
theorem energy_lower_of_heat_bound {t q E : ℝ}
    (ht : 0 < t) (_hq : 0 < q)
    (h : Real.exp (-t * E) ≤ q) : -Real.log q / t ≤ E := by
  have hlog := Real.log_le_log (Real.exp_pos (-t * E)) h
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ ht).mpr
  nlinarith

/-- Original #16's spectral implication, for an actual possibly unbounded
operator and its full resolvent-complement spectrum. The standard unbounded
spectral-calculus interface is displayed, never installed as a new axiom. -/
theorem original16_generator_gap
    (A : H →ₗ.[ℂ] H) (T : H →L[ℂ] H) (t q : ℝ)
    (ht : 0 < t) (hq0 : 0 < q) (hq1 : q < 1)
    (hcalc : HeatSpectralInput A t T)
    (hform : ∀ x : H, (⟪T x, x⟫_ℂ).re ≤ q * ‖x‖ ^ 2) :
    0 < -Real.log q / t ∧
      ∀ z ∈ generatorSpectrum A, z.im = 0 ∧ -Real.log q / t ≤ z.re := by
  constructor
  · exact div_pos (neg_pos.mpr (Real.log_neg hq0 hq1)) ht
  · intro z hz
    have him := hcalc.real_spectrum z hz
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using him.symm
    have hmap := hcalc.heat_spectral_inclusion z.re (by simpa only [hzreal] using hz)
    have hb := transfer_spectrum_le T q (Real.exp (-t * z.re)) hform hmap
    exact ⟨him, energy_lower_of_heat_bound ht hq0 hb⟩

/-- Original physical-scale conversion, with its original positivity and
terminal-spacing input. No scheme identification or scale limit is proved here. -/
theorem physical_gap_scale_lower {q a cPlus Lambda : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (hc : 0 < cPlus) (hLambda : 0 < Lambda)
    (hscale : a ≤ cPlus / Lambda) :
    0 < (-Real.log q / (2 * cPlus)) * Lambda ∧
      (-Real.log q / (2 * cPlus)) * Lambda ≤ -Real.log q / (2 * a) := by
  have hlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hac : a * Lambda ≤ cPlus := (le_div_iff₀ hLambda).mp hscale
  constructor
  · exact mul_pos (div_pos hlog (by positivity)) hLambda
  · apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    have h1 : ((-Real.log q / (2 * cPlus)) * Lambda) * (2 * a) =
        (-Real.log q / cPlus) * (a * Lambda) := by ring
    rw [h1]
    calc
      (-Real.log q / cPlus) * (a * Lambda) ≤ (-Real.log q / cPlus) * cPlus :=
        mul_le_mul_of_nonneg_left hac (div_nonneg hlog.le hc.le)
      _ = -Real.log q := div_mul_cancel₀ _ hc.ne'

#print axioms transfer_resolvent_above_bound
#print axioms original16_generator_gap
#print axioms physical_gap_scale_lower
end YMUIC.ConditionalI7
