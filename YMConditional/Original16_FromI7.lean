import YMConditional.Original16_SpectralPackets
import Mathlib.Data.EReal.Basic

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.ConditionalI7
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Infimum of the complete nonvacuum generator spectrum, with empty spectrum
assigned +infinity rather than the real sInf junk value zero. -/
def generatorGap (A : H →ₗ.[ℂ] H) : EReal :=
  sInf ((fun z : ℂ => (z.re : EReal)) '' generatorSpectrum A)

omit [CompleteSpace H] in
theorem generatorGap_lower (A : H →ₗ.[ℂ] H) (d : ℝ)
    (h : ∀ z ∈ generatorSpectrum A, d ≤ z.re) : (d : EReal) ≤ generatorGap A := by
  apply le_sInf
  rintro _ ⟨z, hz, rfl⟩
  change (d : EReal) ≤ (z.re : EReal)
  exact_mod_cast h z hz

/-- Original #16, linked to the SAME vacuum restriction and original #15.
The only unresolved Yang--Mills node used here is the displayed hI7.
Standard unbounded spectral-calculus input hSpectral is independently
identified and remains explicit; it is NOT counted as kernel-proved here.
The physical-scale upper bound is exactly the original paper premise (186).
No boundedness, compactness or eigenbasis of the generator is assumed. -/
theorem original16_mass_gap_from_I7
    (Ω : H) (v : ι → H) (T : H →L[ℂ] H)
    (η a cPlus Lambda : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (ha : 0 < a) (hc : 0 < cPlus) (hLambda : 0 < Lambda)
    (hT : T.IsPositive) (hfix : T Ω = Ω)
    (hdense : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (hI7 : I7Gram (fun i => center Ω (v i)) T η)
    (A : vacuumSector Ω →ₗ.[ℂ] vacuumSector Ω)
    (hSpectral : NonnegativeHeatCalculus A (2 * a)
      (vacuumTransfer Ω T hT.isSelfAdjoint hfix))
    (hscale : a ≤ cPlus / Lambda) :
    0 < -Real.log (1 - η) / (2 * a) ∧
    0 < (-Real.log (1 - η) / (2 * cPlus)) * Lambda ∧
    (-Real.log (1 - η) / (2 * cPlus)) * Lambda ≤
      -Real.log (1 - η) / (2 * a) ∧
    ((-Real.log (1 - η) / (2 * a) : ℝ) : EReal) ≤ generatorGap A ∧
    (∀ z ∈ generatorSpectrum A,
      z.im = 0 ∧ -Real.log (1 - η) / (2 * a) ≤ z.re) := by
  have hq0 : 0 < 1 - η := sub_pos.mpr hη1
  have hq1 : 1 - η < 1 := by linarith
  have ht : 0 < 2 * a := mul_pos (by norm_num) ha
  have hform : ∀ x : vacuumSector Ω,
      (⟪vacuumTransfer Ω T hT.isSelfAdjoint hfix x, x⟫_ℂ).re ≤
        (1 - η) * ‖x‖ ^ 2 := by
    intro x
    have hx : ⟪Ω, x.val⟫_ℂ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    have h := original15_transfer_from_I7 Ω v T η hdense hI7 x.val hx
    change (⟪T x.val, x.val⟫_ℂ).re ≤ (1 - η) * ‖x.val‖ ^ 2
    have hsym : (⟪T x.val, x.val⟫_ℂ).re = (⟪x.val, T x.val⟫_ℂ).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym]
    exact h
  have hg := original16_generator_gap A
    (vacuumTransfer Ω T hT.isSelfAdjoint hfix) (2 * a) (1 - η)
    ht hq0 hq1 (hSpectral.toHeatSpectralInput ht) hform
  have hs := physical_gap_scale_lower hq0 hq1 ha hc hLambda hscale
  exact ⟨hg.1, hs.1, hs.2, generatorGap_lower A _ (fun z hz => (hg.2 z hz).2), hg.2⟩

/-- A cofinality/uniformity-safe corollary: the SAME eta, physical Lambda and
upper spacing constant serve every regulator. No Hilbert spaces at different
regulators are identified. The original per-regulator theorem is applied
pointwise before any continuum construction. -/
theorem uniform_spectral_scale_lower
    {κ : Type*} (S : κ → Set ℂ) (a : κ → ℝ)
    (q cPlus Lambda : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < cPlus) (hLambda : 0 < Lambda)
    (ha : ∀ k, 0 < a k)
    (hscale : ∀ k, a k ≤ cPlus / Lambda)
    (hspectral : ∀ k z, z ∈ S k → -Real.log q / (2 * a k) ≤ z.re) :
    0 < (-Real.log q / (2 * cPlus)) * Lambda ∧
      ∀ k z, z ∈ S k → (-Real.log q / (2 * cPlus)) * Lambda ≤ z.re := by
  constructor
  · exact mul_pos (div_pos (neg_pos.mpr (Real.log_neg hq0 hq1))
      (mul_pos (by norm_num) hc)) hLambda
  · intro k z hz
    exact (physical_gap_scale_lower hq0 hq1 (ha k) hc hLambda (hscale k)).2.trans
      (hspectral k z hz)


/-- Uniform original-16 conclusion over unrelated regulator Hilbert spaces.
The constants eta, cPlus and Lambda are outside the regulator quantifier. -/
theorem original16_uniform_mass_gap_from_I7
    {κ : Type*} (V : κ → Type*) (I : Type*)
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℂ (V k)]
    [∀ k, CompleteSpace (V k)]
    (Ω : ∀ k, V k) (v : ∀ k, I → V k) (T : ∀ k, V k →L[ℂ] V k)
    (η cPlus Lambda : ℝ) (a : κ → ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hc : 0 < cPlus) (hLambda : 0 < Lambda)
    (ha : ∀ k, 0 < a k) (hT : ∀ k, (T k).IsPositive)
    (hfix : ∀ k, T k (Ω k) = Ω k)
    (hdense : ∀ k, Dense (Submodule.span ℂ (Set.range (v k)) : Set (V k)))
    (hI7 : ∀ k, I7Gram (fun i => center (Ω k) (v k i)) (T k) η)
    (A : ∀ k, vacuumSector (Ω k) →ₗ.[ℂ] vacuumSector (Ω k))
    (hSpectral : ∀ k, NonnegativeHeatCalculus (A k) (2 * a k)
      (vacuumTransfer (Ω k) (T k) (hT k).isSelfAdjoint (hfix k)))
    (hscale : ∀ k, a k ≤ cPlus / Lambda) :
    0 < (-Real.log (1 - η) / (2 * cPlus)) * Lambda ∧
      ∀ k, (((-Real.log (1 - η) / (2 * cPlus)) * Lambda : ℝ) : EReal) ≤
        generatorGap (A k) := by
  constructor
  · exact mul_pos (div_pos (neg_pos.mpr (Real.log_neg (by linarith) (by linarith)))
      (mul_pos (by norm_num) hc)) hLambda
  · intro k
    have h := original16_mass_gap_from_I7 (Ω k) (v k) (T k) η (a k) cPlus Lambda
      hη0 hη1 (ha k) hc hLambda (hT k) (hfix k) (hdense k) (hI7 k)
      (A k) (hSpectral k) (hscale k)
    have hb : (((-Real.log (1 - η) / (2 * cPlus)) * Lambda : ℝ) : EReal) ≤
        ((-Real.log (1 - η) / (2 * a k) : ℝ) : EReal) := by
      exact_mod_cast h.2.2.1
    exact hb.trans h.2.2.2.1

#print axioms original16_uniform_mass_gap_from_I7
#print axioms generatorGap_lower
#print axioms original16_mass_gap_from_I7
#print axioms uniform_spectral_scale_lower
end YMUIC.ConditionalI7
