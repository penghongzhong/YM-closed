import YMConditional.Original40_L2Gram
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

noncomputable section
namespace YMUIC.ConditionalI7
open MeasureTheory Filter
open scoped Topology InnerProductSpace

/-- Original #40 / Theorem 20.1. The original reference-root normalization
and deficit estimate (399) remain explicit. The positive variance conclusion
and its L2 dictionary are outputs. The positive operator is the SAME T as in
that deficit; no auxiliary dynamics is substituted. -/
theorem original40_variance_lower_bound
    {X H E0 : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E0]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ)
    (J : Lp ℂ 2 μ →ₗᵢ[ℂ] H)
    (T : H →L[ℂ] H) (hT : T.IsPositive)
    (referenceRoot : (X → ℝ) → E0) (ΩB : ℝ)
    (hreference : ‖referenceRoot F‖^2 = 1)
    (hdeficit399 : Real.exp (-2 * ΩB) * ‖referenceRoot F‖^2 ≤
      transferDeficit T (J (centeredVector μ F hF))) :
    ‖J (centeredVector μ F hF)‖^2 = cutoffVariance μ F ∧
    Real.exp (-2 * ΩB) ≤ cutoffVariance μ F ∧
    0 < cutoffVariance μ F ∧
    J (centeredVector μ F hF) ≠ 0 := by
  have hnorm : ‖J (centeredVector μ F hF)‖^2 = cutoffVariance μ F := by
    rw [J.norm_map, centeredVector_norm_sq]
  have hbound : Real.exp (-2 * ΩB) ≤ cutoffVariance μ F := by
    have hd : Real.exp (-2 * ΩB) ≤ transferDeficit T (J (centeredVector μ F hF)) := by
      simpa only [hreference, mul_one] using hdeficit399
    exact hd.trans (physical_deficit_le_variance μ F hF J T hT)
  have hpos := (Real.exp_pos (-2 * ΩB)).trans_le hbound
  refine ⟨hnorm, hbound, hpos, ?_⟩
  intro hz
  rw [hz, norm_zero, zero_pow (by decide)] at hnorm
  linarith

/-- One fixed Omega_B and hence one fixed positive c_B for the whole cutoff-
volume family. Probability spaces, physical Hilbert spaces and reference
spaces may vary. No identification between different cutoffs is made. -/
theorem original40_uniform_variance
    {ι : Type*} {X H E0 : ι → Type*}
    [∀ i, MeasurableSpace (X i)]
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, NormedAddCommGroup (E0 i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (i : ι) → X i → ℝ) (hF : ∀ i, MemLp (F i) 2 (μ i))
    (J : (i : ι) → Lp ℂ 2 (μ i) →ₗᵢ[ℂ] H i)
    (T : (i : ι) → H i →L[ℂ] H i) (hT : ∀ i, (T i).IsPositive)
    (referenceRoot : (i : ι) → (X i → ℝ) → E0 i) (ΩB : ℝ)
    (hreference : ∀ i, ‖referenceRoot i (F i)‖^2 = 1)
    (hdeficit399 : ∀ i, Real.exp (-2 * ΩB) * ‖referenceRoot i (F i)‖^2 ≤
      transferDeficit (T i) (J i (centeredVector (μ i) (F i) (hF i)))) :
    0 < Real.exp (-2 * ΩB) ∧
    ∀ i, ‖J i (centeredVector (μ i) (F i) (hF i))‖^2 = cutoffVariance (μ i) (F i) ∧
      Real.exp (-2 * ΩB) ≤ cutoffVariance (μ i) (F i) ∧
      0 < cutoffVariance (μ i) (F i) ∧
      J i (centeredVector (μ i) (F i) (hF i)) ≠ 0 := by
  refine ⟨Real.exp_pos _, ?_⟩
  intro i
  exact original40_variance_lower_bound (μ i) (F i) (hF i) (J i) (T i) (hT i)
    (referenceRoot i) ΩB (hreference i) (hdeficit399 i)

/-- The physical L2 realization can be the identity. This concrete reading
needs no abstract Gram/norm dictionary or substitute variance premise. -/
theorem original40_on_actual_L2
    {X E0 : Type*} [MeasurableSpace X] [NormedAddCommGroup E0]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : T.IsPositive)
    (referenceRoot : (X → ℝ) → E0) (ΩB : ℝ)
    (hreference : ‖referenceRoot F‖^2 = 1)
    (hdeficit399 : Real.exp (-2 * ΩB) * ‖referenceRoot F‖^2 ≤
      transferDeficit T (centeredVector μ F hF)) :
    Real.exp (-2 * ΩB) ≤ cutoffVariance μ F ∧ 0 < cutoffVariance μ F := by
  have h := original40_variance_lower_bound μ F hF (LinearIsometry.id) T hT
    referenceRoot ΩB hreference hdeficit399
  exact ⟨h.2.1, h.2.2.1⟩

/-- Bounded cylinders are L2 without a cutoff-uniform bound on their sup norm. -/
theorem boundedCylinder_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ)
    (hmeas : AEStronglyMeasurable F μ)
    (hbounded : ∃ M : ℝ, ∀ᵐ x ∂μ, ‖F x‖ ≤ M) : MemLp F 2 μ := by
  obtain ⟨M, hM⟩ := hbounded
  exact MemLp.of_bound hmeas M hM

/-- Original bounded-cylinder family statement. Integrability, the actual
L2 variance identity and the positive constant are all derived. -/
theorem original40_bounded_cylinder_uniform
    {ι : Type*} {X H E0 : ι → Type*}
    [∀ i, MeasurableSpace (X i)]
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, NormedAddCommGroup (E0 i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (i : ι) → X i → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (F i) (μ i))
    (hbounded : ∀ i, ∃ M : ℝ, ∀ᵐ x ∂μ i, ‖F i x‖ ≤ M)
    (J : (i : ι) → Lp ℂ 2 (μ i) →ₗᵢ[ℂ] H i)
    (T : (i : ι) → H i →L[ℂ] H i) (hT : ∀ i, (T i).IsPositive)
    (referenceRoot : (i : ι) → (X i → ℝ) → E0 i) (ΩB : ℝ)
    (hreference : ∀ i, ‖referenceRoot i (F i)‖^2 = 1)
    (hdeficit399 : ∀ i, Real.exp (-2 * ΩB) * ‖referenceRoot i (F i)‖^2 ≤
      transferDeficit (T i) (J i (centeredVector (μ i) (F i)
        (boundedCylinder_memLp (μ i) (F i) (hmeas i) (hbounded i))))) :
    0 < Real.exp (-2 * ΩB) ∧
      ∀ i, Real.exp (-2 * ΩB) ≤ cutoffVariance (μ i) (F i) ∧
        0 < cutoffVariance (μ i) (F i) := by
  have h := original40_uniform_variance μ F
    (fun i => boundedCylinder_memLp (μ i) (F i) (hmeas i) (hbounded i))
    J T hT referenceRoot ΩB hreference hdeficit399
  exact ⟨h.1, fun i => ⟨(h.2 i).2.1, (h.2 i).2.2.1⟩⟩

end YMUIC.ConditionalI7
