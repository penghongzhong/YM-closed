import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace YMUIC.ConditionalI7
open Filter MeasureTheory
open scoped Topology

/-- The actual centered second moment. Integrability is supplied when this is
used, so the Bochner integral's default value cannot conceal divergence. -/
def cutoffVariance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ) : ℝ :=
  ∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ

theorem cutoffVariance_eq_moments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hL2 : MemLp F 2 μ) :
    cutoffVariance μ F = (∫ x, (F x)^2 ∂μ) - (∫ x, F x ∂μ)^2 := by
  simp only [cutoffVariance, sub_sq']
  rw [integral_sub, integral_add]
  · simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
      integral_mul_const, integral_const_mul]
    ring
  · exact hL2.integrable_sq
  · exact integrable_const _
  · exact hL2.integrable_sq.add (integrable_const _)
  · exact ((hL2.integrable (by norm_num)).const_mul 2).mul_const' _

/-- The directed cutoff-volume filter is nontrivial. Both moments belong to
one and the same observable family; the probability spaces may vary. -/
theorem original41_variance_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (i : ι) → X i → ℝ) (hL2 : ∀ i, MemLp (F i) 2 (μ i))
    {m₁ m₂ c : ℝ}
    (hfirst : Tendsto (fun i => ∫ x, F i x ∂μ i) l (𝓝 m₁))
    (hsecond : Tendsto (fun i => ∫ x, (F i x)^2 ∂μ i) l (𝓝 m₂))
    (hvar : ∀ᶠ i in l, c ≤ cutoffVariance (μ i) (F i)) :
    Tendsto (fun i => cutoffVariance (μ i) (F i)) l (𝓝 (m₂-m₁^2)) ∧
      c ≤ m₂-m₁^2 := by
  have hident : (fun i => cutoffVariance (μ i) (F i)) =
      (fun i => (∫ x, (F i x)^2 ∂μ i) - (∫ x, F i x ∂μ i)^2) := by
    funext i
    exact cutoffVariance_eq_moments (μ i) (F i) (hL2 i)
  have hlim : Tendsto (fun i => cutoffVariance (μ i) (F i)) l (𝓝 (m₂-m₁^2)) := by
    rw [hident]
    exact hsecond.sub (hfirst.pow 2)
  exact ⟨hlim, ge_of_tendsto hlim hvar⟩

#print axioms original41_variance_limit
end YMUIC.ConditionalI7
