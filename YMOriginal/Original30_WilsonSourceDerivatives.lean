import YM.OSGrowth.BoundedProbabilitySource
import YMOriginal.Original30_WilsonObservableContinuity

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction

namespace YMUIC.Original30
open YMUIC.Original24 YMUICV128.Section03

/-- Actual Wilson word polynomial as a bounded continuous observable.
Its bound follows from the proved SU(2) polynomial budget. -/
def actualWilsonObservableBCF
    {Ω W T : Type*} [TopologicalSpace Ω] [Fintype T]
    (U : Ω → W → SU2) (words : T → List (List W)) (coeff : T → ℂ)
    (hcont : Continuous (fun ω => actualWilsonPolynomial (U ω) words coeff)) : Ω →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ω => actualWilsonPolynomial (U ω) words coeff, hcont⟩
    (2 * actualWilsonPolynomialBudget words coeff) (by
      intro x y
      calc
        _ ≤ ‖actualWilsonPolynomial (U x) words coeff‖ +
            ‖actualWilsonPolynomial (U y) words coeff‖ := by
              rw [dist_eq_norm]
              exact norm_sub_le _ _
        _ ≤ 2 * actualWilsonPolynomialBudget words coeff := by
          linarith [actual_wilson_polynomial_bound (U x) words coeff,
            actual_wilson_polynomial_bound (U y) words coeff])

/-- The finite source is a continuous linear map into the observable algebra. -/
def actualWilsonSourceCLM
    {Ω P W T : Type*} [TopologicalSpace Ω] [Fintype P] [Fintype T]
    (weights : P → ℂ) (U : Ω → P → W → SU2)
    (words : P → T → List (List W)) (coeff : P → T → ℂ)
    (hcont : ∀ p, Continuous (fun ω => actualWilsonPolynomial (U ω p) (words p) (coeff p))) :
    (P → ℂ) →L[ℂ] (Ω →ᵇ ℂ) :=
  ∑ p : P, (ContinuousLinearMap.proj p).smulRight
    (weights p • actualWilsonObservableBCF (fun ω => U ω p) (words p) (coeff p) (hcont p))

/-- Genuine finite-regulator partition function, normalized by a probability law. -/
def actualWilsonGeneratingFunction
    {Ω P W T : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype T]
    (μ : Measure Ω) (weights : P → ℂ) (U : Ω → P → W → SU2)
    (words : P → T → List (List W)) (coeff : P → T → ℂ) (J : P → ℂ) : ℂ :=
  ∫ ω, Complex.exp (∑ p : P,
    weights p * J p * actualWilsonPolynomial (U ω p) (words p) (coeff p)) ∂μ

/-- Exact arbitrary mixed derivatives of the actual finite Wilson source.
No moment dictionary, analytic radius, differentiation-under-integral rule,
or regulator-uniform bound is assumed. The result is at each finite regulator. -/
theorem actual_wilson_source_derivatives
    {Ω P W T : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [Fintype P] [Fintype T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weights : P → ℂ) (U : Ω → P → W → SU2)
    (words : P → T → List (List W)) (coeff : P → T → ℂ)
    (hU : ∀ p w, Continuous (fun ω => U ω p w)) :
    let Z := actualWilsonGeneratingFunction μ weights U words coeff
    AnalyticOnNhd ℂ Z Set.univ ∧ Z 0 = 1 ∧
    ∀ (r : ℕ) (h : Fin r → P → ℂ),
      iteratedFDeriv ℂ r Z 0 h =
        ∫ ω, ∏ j, ∑ p : P, weights p * h j p *
          actualWilsonPolynomial (U ω p) (words p) (coeff p) ∂μ := by
  have hcont (p : P) : Continuous
      (fun ω => actualWilsonPolynomial (U ω p) (words p) (coeff p)) :=
    actual_wilson_polynomial_continuous (fun ω => U ω p) (hU p) (words p) (coeff p)
  let source := actualWilsonSourceCLM weights U words coeff hcont
  have happly (J : P → ℂ) (ω : Ω) : source J ω =
      ∑ p : P, weights p * J p * actualWilsonPolynomial (U ω p) (words p) (coeff p) := by
    simp only [source, actualWilsonSourceCLM, sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    change J p * (weights p * actualWilsonPolynomial (U ω p) (words p) (coeff p)) = _
    ring
  have h := YMUIC.OSGrowth.bounded_probability_source_derivatives μ source
  simp_rw [happly] at h
  exact h

end YMUIC.Original30
