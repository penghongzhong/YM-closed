import YMConditional.Original41_GNS

set_option autoImplicit false

noncomputable section
namespace YMUIC.ConditionalI7
open Filter MeasureTheory
open scoped Topology InnerProductSpace ComplexConjugate

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Original #41, paper Theorem 20.2: the SAME bounded observable's first
and second moments converge along one nontrivial cutoff-volume net. The
uniform positive variance bound is exactly original #40, not a consequence
of I7 alone. The GNS identity is the defining state/inner-product dictionary.
No Hilbert spaces at different cutoffs are identified. -/
theorem original41_continuum_nontriviality
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Fcut : (i : ι) → X i → ℝ)
    (hL2 : ∀ i, MemLp (Fcut i) 2 (μ i))
    (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1)
    (F : A) (hF : star F = F) {c : ℝ} (hc : 0 < c)
    (hfirst : Tendsto (fun i => ∫ x, Fcut i x ∂μ i) l (𝓝 (ω F).re))
    (hsecond : Tendsto (fun i => ∫ x, (Fcut i x)^2 ∂μ i) l
      (𝓝 (ω (F*F)).re))
    (hvar40 : ∀ᶠ i in l, c ≤ cutoffVariance (μ i) (Fcut i)) :
    c ≤ (ω (F*F)).re - (ω F).re^2 ∧
    ω (F*F) ≠ ω F * ω F ∧
    (∃ v : H, ⟪J 1, v⟫_ℂ = 0 ∧ c ≤ ‖v‖^2 ∧ v ≠ 0 ∧
      v ∉ Submodule.span ℂ ({J 1} : Set H)) ∧
    Submodule.span ℂ ({J 1} : Set H) ≠ ⊤ := by
  have hv := (original41_variance_limit μ Fcut hL2 hfirst hsecond hvar40).2
  have him := (gns_selfadjoint_moments ω J hGNS F hF).2.2.2
  have hnot : ω (F*F) ≠ ω F * ω F := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.mul_re, him, mul_zero, sub_zero] at hre
    nlinarith
  obtain ⟨v, ho, hb, hn, hs⟩ :=
    gns_nontrivial_of_positive_variance ω J hGNS hunit F hF hc hv
  refine ⟨hv, hnot, ⟨v, ho, hb, hn, hs⟩, ?_⟩
  intro heq
  apply hs
  rw [heq]
  exact Submodule.mem_top

/-- Original bounded-cylinder form, deriving L2 integrability from
measurability and a finite bound at each cutoff. No uniform L-infinity bound
is invented and no integrability conclusion is silently assumed. -/
theorem original41_bounded_cylinder_net
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Fcut : (i : ι) → X i → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (Fcut i) (μ i))
    (hbounded : ∀ i, ∃ M : ℝ, ∀ᵐ x ∂μ i, ‖Fcut i x‖ ≤ M)
    (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1)
    (F : A) (hF : star F = F) {c : ℝ} (hc : 0 < c)
    (hfirst : Tendsto (fun i => ∫ x, Fcut i x ∂μ i) l (𝓝 (ω F).re))
    (hsecond : Tendsto (fun i => ∫ x, (Fcut i x)^2 ∂μ i) l
      (𝓝 (ω (F*F)).re))
    (hvar40 : ∀ᶠ i in l, c ≤ cutoffVariance (μ i) (Fcut i)) :
    c ≤ (ω (F*F)).re - (ω F).re^2 ∧
    ω (F*F) ≠ ω F * ω F ∧
    (∃ v : H, ⟪J 1, v⟫_ℂ = 0 ∧ c ≤ ‖v‖^2 ∧ v ≠ 0 ∧
      v ∉ Submodule.span ℂ ({J 1} : Set H)) ∧
    Submodule.span ℂ ({J 1} : Set H) ≠ ⊤ := by
  have hL2 : ∀ i, MemLp (Fcut i) 2 (μ i) := by
    intro i
    obtain ⟨M, hM⟩ := hbounded i
    exact MemLp.of_bound (hmeas i) M hM
  exact original41_continuum_nontriviality μ Fcut hL2 ω J hGNS hunit F hF
    hc hfirst hsecond hvar40

#print axioms original41_continuum_nontriviality
#print axioms original41_bounded_cylinder_net
end YMUIC.ConditionalI7
