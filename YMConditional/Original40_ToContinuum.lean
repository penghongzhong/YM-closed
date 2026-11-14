import YMConditional.Original40_UniformVariance
import YMConditional.Original41_Nontriviality

set_option autoImplicit false

noncomputable section
namespace YMUIC.ConditionalI7
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate

/-- The original40 producer is now actually used by original41: no positive
variance assumption hvar40 is supplied to this composition. The original
transfer-deficit certificate, same-family joint limits and continuum state/GNS
realization remain explicit upstream data. -/
theorem original40_to_original41_nontriviality
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {X H E0 : ι → Type*}
    [∀ i, MeasurableSpace (X i)]
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, NormedAddCommGroup (E0 i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Fcut : (i : ι) → X i → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (Fcut i) (μ i))
    (hbounded : ∀ i, ∃ M : ℝ, ∀ᵐ x ∂μ i, ‖Fcut i x‖ ≤ M)
    (Jcut : (i : ι) → Lp ℂ 2 (μ i) →ₗᵢ[ℂ] H i)
    (T : (i : ι) → H i →L[ℂ] H i) (hT : ∀ i, (T i).IsPositive)
    (referenceRoot : (i : ι) → (X i → ℝ) → E0 i) (ΩB : ℝ)
    (hreference : ∀ i, ‖referenceRoot i (Fcut i)‖^2 = 1)
    (hdeficit399 : ∀ i, Real.exp (-2 * ΩB) * ‖referenceRoot i (Fcut i)‖^2 ≤
      transferDeficit (T i) (Jcut i (centeredVector (μ i) (Fcut i)
        (boundedCylinder_memLp (μ i) (Fcut i) (hmeas i) (hbounded i)))))
    {A G : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] G)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1)
    (F : A) (hF : star F = F)
    (hfirst : Tendsto (fun i => ∫ x, Fcut i x ∂μ i) l (𝓝 (ω F).re))
    (hsecond : Tendsto (fun i => ∫ x, (Fcut i x)^2 ∂μ i) l (𝓝 (ω (F * F)).re)) :
    0 < Real.exp (-2 * ΩB) ∧
    Real.exp (-2 * ΩB) ≤ (ω (F*F)).re - (ω F).re^2 ∧
    ω (F*F) ≠ ω F * ω F ∧
    (∃ v : G, ⟪J 1, v⟫_ℂ = 0 ∧ Real.exp (-2 * ΩB) ≤ ‖v‖^2 ∧ v ≠ 0 ∧
      v ∉ Submodule.span ℂ ({J 1} : Set G)) ∧
    Submodule.span ℂ ({J 1} : Set G) ≠ ⊤ := by
  have h40 := original40_bounded_cylinder_uniform μ Fcut hmeas hbounded
    Jcut T hT referenceRoot ΩB hreference hdeficit399
  refine ⟨h40.1, ?_⟩
  exact original41_bounded_cylinder_net μ Fcut hmeas hbounded
    ω J hGNS hunit F hF h40.1 hfirst hsecond
    (Filter.Eventually.of_forall (fun i => (h40.2 i).1))

end YMUIC.ConditionalI7
