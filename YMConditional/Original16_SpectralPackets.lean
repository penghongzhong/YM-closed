import YMConditional.Original16_SpectralGap

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.ConditionalI7
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Approximate eigenvectors, with arbitrary residual accuracy, imply membership
in the actual Banach-algebra spectrum. No eigenvector, compactness, finite
spectral decomposition or point-spectrum hypothesis is used. -/
theorem spectrum_of_approximate_vectors
    (T : H →L[ℂ] H) (z : ℂ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x : H,
      ‖x‖ = 1 ∧ ‖T x - z • x‖ < ε) : z ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  let R : H →L[ℂ] H := ↑u⁻¹
  let C : ℝ := ‖R‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨x, hx, hres⟩ := happrox (1 / C) (div_pos zero_lt_one hC)
  have hleft : R ((algebraMap ℂ (H →L[ℂ] H) z - T) x) = x := by
    rw [← hu]
    change (↑u⁻¹ : H →L[ℂ] H) ((↑u : H →L[ℂ] H) x) = x
    have h := congrArg (fun F : H →L[ℂ] H => F x) u.inv_val
    exact h
  have hnorm : ‖(algebraMap ℂ (H →L[ℂ] H) z - T) x‖ = ‖T x - z • x‖ := by
    simp only [Algebra.algebraMap_eq_smul_one, sub_apply,
      smul_apply, one_apply_eq_self]
    exact norm_sub_rev _ _
  have hbound : 1 ≤ C * ‖T x - z • x‖ := by
    calc
      1 = ‖x‖ := hx.symm
      _ = ‖R ((algebraMap ℂ (H →L[ℂ] H) z - T) x)‖ := by rw [hleft]
      _ ≤ ‖R‖ * ‖(algebraMap ℂ (H →L[ℂ] H) z - T) x‖ := R.le_opNorm _
      _ ≤ C * ‖T x - z • x‖ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)
  have hlt : C * ‖T x - z • x‖ < 1 := by
    have h := mul_lt_mul_of_pos_left hres hC
    simpa [div_eq_mul_inv, hC.ne'] using h
  linarith

/-- Named standard spectral-calculus input for a possibly unbounded,
nonnegative self-adjoint A and T=exp(-t A), t>0.

The spectral theorem / Weyl criterion supplies spectral_packets. The
functional-calculus Lipschitz estimate |e^(-t x)-e^(-t E)|<=t|x-E|, x,E>=0,
supplies heat_residual. No I7 or positive spectral gap is present here.
These external inputs are NOT kernel-proved by this file; they are explicit
parameters of the original16 standard-input-assisted verification tier. -/
structure NonnegativeHeatCalculus
    (A : H →ₗ.[ℂ] H) (t : ℝ) (T : H →L[ℂ] H) : Prop where
  selfadjoint : IsSelfAdjoint A
  nonnegative : ∀ x : A.domain, 0 ≤ (⟪A x, (x : H)⟫_ℂ).re
  spectrum_real_nonnegative : ∀ z ∈ generatorSpectrum A, z.im = 0 ∧ 0 ≤ z.re
  spectral_packets : ∀ E : ℝ, (E : ℂ) ∈ generatorSpectrum A →
    ∀ ε : ℝ, 0 < ε → ∃ x : A.domain,
      ‖(x : H)‖ = 1 ∧ ‖A x - (E : ℂ) • (x : H)‖ < ε
  heat_residual : ∀ E : ℝ, 0 ≤ E → ∀ x : A.domain,
    ‖T (x : H) - (Real.exp (-t * E) : ℂ) • (x : H)‖ ≤
      t * ‖A x - (E : ℂ) • (x : H)‖

/-- Derive the required forward heat spectral inclusion from the recorded
standard packet/calculus facts, including continuous spectral points. -/
theorem NonnegativeHeatCalculus.toHeatSpectralInput
    {A : H →ₗ.[ℂ] H} {t : ℝ} {T : H →L[ℂ] H}
    (C : NonnegativeHeatCalculus A t T) (ht : 0 < t) :
    HeatSpectralInput A t T := by
  refine ⟨fun z hz => (C.spectrum_real_nonnegative z hz).1, ?_⟩
  intro E hE
  apply spectrum_of_approximate_vectors
  intro ε hε
  obtain ⟨x, hx, hsmall⟩ := C.spectral_packets E hE (ε / t) (div_pos hε ht)
  refine ⟨x, hx, ?_⟩
  have hE0 : 0 ≤ E := (C.spectrum_real_nonnegative (E : ℂ) hE).2
  calc
    ‖T (x : H) - (Real.exp (-t * E) : ℂ) • (x : H)‖
      ≤ t * ‖A x - (E : ℂ) • (x : H)‖ := C.heat_residual E hE0 x
    _ < t * (ε / t) := mul_lt_mul_of_pos_left hsmall ht
    _ = ε := by field_simp

#print axioms spectrum_of_approximate_vectors
#print axioms NonnegativeHeatCalculus.toHeatSpectralInput
end YMUIC.ConditionalI7
