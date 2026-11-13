import YMConditional.Original41_Nontriviality

set_option autoImplicit false
noncomputable section

namespace YMUIC.ConditionalI7
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate

/-!
# Exact one-observable Bałaban RG readback

The external RG input is intentionally narrow.  For one terminal observable
Xstar and its original-Wilson pullback X0, the published averaging identity
supplies equality of the first two moments.  This is exactly the v98
readback boundary and does not assert a left inverse for the full RG map.
-/

/-- One-observable specialization of the published Bałaban averaging /
delta-constraint push-forward identity. -/
structure PublishedBalabanTerminalReadback
    {X0 Xstar : Type*} [MeasurableSpace X0] [MeasurableSpace Xstar]
    (μ0 : Measure X0) (μstar : Measure Xstar)
    (F0 : X0 → ℝ) (Fstar : Xstar → ℝ) : Prop where
  firstMoment :
    (∫ x, F0 x ∂μ0) = ∫ x, Fstar x ∂μstar
  secondMoment :
    (∫ x, (F0 x)^2 ∂μ0) = ∫ x, (Fstar x)^2 ∂μstar

/-- Exact first/second-moment readback preserves the centered variance. -/
theorem cutoffVariance_eq_of_balaban_readback
    {X0 Xstar : Type*} [MeasurableSpace X0] [MeasurableSpace Xstar]
    (μ0 : Measure X0) [IsProbabilityMeasure μ0]
    (μstar : Measure Xstar) [IsProbabilityMeasure μstar]
    (F0 : X0 → ℝ) (Fstar : Xstar → ℝ)
    (h0 : MemLp F0 2 μ0) (hstar : MemLp Fstar 2 μstar)
    (R : PublishedBalabanTerminalReadback μ0 μstar F0 Fstar) :
    cutoffVariance μ0 F0 = cutoffVariance μstar Fstar := by
  rw [cutoffVariance_eq_moments μ0 F0 h0,
      cutoffVariance_eq_moments μstar Fstar hstar,
      R.firstMoment, R.secondMoment]

/-- Terminal absolute nontriviality plus exact Bałaban readback gives the
original-Wilson variance lower bound needed by the continuum GNS theorem. -/
theorem original_variance_lower_of_terminal_balaban_readback
    {X0 Xstar : Type*} [MeasurableSpace X0] [MeasurableSpace Xstar]
    (μ0 : Measure X0) [IsProbabilityMeasure μ0]
    (μstar : Measure Xstar) [IsProbabilityMeasure μstar]
    (F0 : X0 → ℝ) (Fstar : Xstar → ℝ)
    (h0 : MemLp F0 2 μ0) (hstar : MemLp Fstar 2 μstar)
    (R : PublishedBalabanTerminalReadback μ0 μstar F0 Fstar)
    (c : ℝ) (hterminal : c ≤ cutoffVariance μstar Fstar) :
    c ≤ cutoffVariance μ0 F0 := by
  rw [cutoffVariance_eq_of_balaban_readback
    μ0 μstar F0 Fstar h0 hstar R]
  exact hterminal

/-- Net-level continuum nontriviality from a terminal variance certificate
and exact one-observable Bałaban readback.  No terminal-density reflection
positivity and no full inverse RG reconstruction are used. -/
theorem original41_continuum_nontriviality_from_balaban_readback
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {X0 Xstar : ι → Type*}
    [∀ i, MeasurableSpace (X0 i)]
    [∀ i, MeasurableSpace (Xstar i)]
    (μ0 : (i : ι) → Measure (X0 i))
    [∀ i, IsProbabilityMeasure (μ0 i)]
    (μstar : (i : ι) → Measure (Xstar i))
    [∀ i, IsProbabilityMeasure (μstar i)]
    (F0 : (i : ι) → X0 i → ℝ)
    (Fstar : (i : ι) → Xstar i → ℝ)
    (h0 : ∀ i, MemLp (F0 i) 2 (μ0 i))
    (hstar : ∀ i, MemLp (Fstar i) 2 (μstar i))
    (R : ∀ i, PublishedBalabanTerminalReadback
      (μ0 i) (μstar i) (F0 i) (Fstar i))
    {A H : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1)
    (F : A) (hF : star F = F)
    {c : ℝ} (hc : 0 < c)
    (hterminal : ∀ᶠ i in l,
      c ≤ cutoffVariance (μstar i) (Fstar i))
    (hfirst : Tendsto (fun i => ∫ x, F0 i x ∂μ0 i)
      l (𝓝 (ω F).re))
    (hsecond : Tendsto (fun i => ∫ x, (F0 i x)^2 ∂μ0 i)
      l (𝓝 (ω (F*F)).re)) :
    c ≤ (ω (F*F)).re - (ω F).re^2 ∧
    ω (F*F) ≠ ω F * ω F ∧
    (∃ v : H, ⟪J 1, v⟫_ℂ = 0 ∧ c ≤ ‖v‖^2 ∧ v ≠ 0 ∧
      v ∉ Submodule.span ℂ ({J 1} : Set H)) ∧
    Submodule.span ℂ ({J 1} : Set H) ≠ ⊤ := by
  have hvar0 : ∀ᶠ i in l,
      c ≤ cutoffVariance (μ0 i) (F0 i) := by
    filter_upwards [hterminal] with i hi
    exact original_variance_lower_of_terminal_balaban_readback
      (μ0 i) (μstar i) (F0 i) (Fstar i)
      (h0 i) (hstar i) (R i) c hi
  exact original41_continuum_nontriviality
    μ0 F0 h0 ω J hGNS hunit F hF hc hfirst hsecond hvar0

#print axioms cutoffVariance_eq_of_balaban_readback
#print axioms original_variance_lower_of_terminal_balaban_readback
#print axioms original41_continuum_nontriviality_from_balaban_readback

end YMUIC.ConditionalI7
