import YM.OSGrowth.ExponentialSourceDerivatives
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction

namespace YMUIC.OSGrowth

/-- Actual expectation of bounded continuous complex observables. -/
def probabilityExpectation
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : (Ω →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ ω, f ω ∂μ
      map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun c f => integral_smul c f }
    1 (fun f => by simpa using f.norm_integral_le_norm μ)

/-- Differentiation of the actual exponential expectation to ALL orders.
No derivative-under-integral identity is assumed. Completeness of the
bounded continuous function algebra and boundedness of expectation prove it. -/
theorem bounded_probability_source_derivatives
    {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (source : E →L[ℂ] (Ω →ᵇ ℂ)) :
    let Z : E → ℂ := fun J => ∫ ω, Complex.exp (source J ω) ∂μ
    AnalyticOnNhd ℂ Z Set.univ ∧ Z 0 = 1 ∧
    ∀ (r : ℕ) (h : Fin r → E),
      iteratedFDeriv ℂ r Z 0 h = ∫ ω, ∏ j, source (h j) ω ∂μ := by
  let Z : E → ℂ := fun J => ∫ ω, Complex.exp (source J ω) ∂μ
  have he (J : E) (ω : Ω) :
      (NormedSpace.exp (source J)) ω = Complex.exp (source J ω) := by
    let ev : (Ω →ᵇ ℂ) →+* ℂ :=
      { toFun := fun f => f ω
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have h := NormedSpace.map_exp ev (BoundedContinuousFunction.evalCLM ℂ ω).continuous
      (source J)
    change (NormedSpace.exp (source J)) ω = NormedSpace.exp (source J ω) at h
    rwa [← Complex.exp_eq_exp_ℂ] at h
  have hfun : (fun J => probabilityExpectation μ (NormedSpace.exp (source J))) = Z := by
    funext J
    change (∫ ω, (NormedSpace.exp (source J)) ω ∂μ) = _
    simp_rw [he]
    rfl
  obtain ⟨han, hd⟩ := exponential_linear_source_derivatives source (probabilityExpectation μ)
  rw [hfun] at han hd
  refine ⟨han, ?_, ?_⟩
  · simp
  · intro r h
    rw [hd r h]
    change (∫ ω, (∏ j, source (h j)) ω ∂μ) = _
    simp only [BoundedContinuousFunction.prod_apply]

end YMUIC.OSGrowth
