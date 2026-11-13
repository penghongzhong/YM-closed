import YMOriginal.Original30_WilsonSourceDerivatives
import YMOriginal.Original30_FixedBoxJointHierarchy

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction

namespace YMUIC.Original30
open YMUIC.Original24 YMUICV128.Section03

/-- A continuous functional on GENERAL joint Schwartz tests constructed
directly from the coordinate derivatives of the actual finite Wilson source. -/
def actualWilsonSourceJointDistribution
    {Ω P W T : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype T]
    (μ : Measure Ω) (weights : P → ℂ) (U : Ω → P → W → SU2)
    (words : P → T → List (List W)) (coeff : P → T → ℂ)
    (r : ℕ) (locations : (Fin r → P) → EuclideanSpace ℝ (Fin (4 * r))) :
    YMUIC.Original34.JointTest r →L[ℂ] ℂ := by
  classical
  exact ∑ tuple : Fin r → P,
    iteratedFDeriv ℂ r (actualWilsonGeneratingFunction μ weights U words coeff) 0
      (fun j => Pi.single (tuple j) (1 : ℂ)) • jointSchwartzEvalCLM r (locations tuple)

/-- The genuine general joint Schwartz moment equals the finite coordinate
reconstruction of the actual exponential Wilson source derivatives. The
test need not factorize. All weights and polynomial coefficients are exact
and arbitrary; this identity itself makes no regulator-uniform estimate. -/
theorem actual_wilson_joint_source_dictionary
    {Ω P W T : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [Fintype P] [Fintype T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weights : P → ℂ) (U : Ω → P → W → SU2)
    (words : P → T → List (List W)) (coeff : P → T → ℂ)
    (hU : ∀ p w, Continuous (fun ω => U ω p w))
    (r : ℕ) (locations : (Fin r → P) → EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r) :
    Integrable (fun ω => actualWordJointCutoff r weights (U ω) words coeff locations f) μ ∧
    actualWilsonSourceJointDistribution μ weights U words coeff r locations f =
      ∫ ω, actualWordJointCutoff r weights (U ω) words coeff locations f ∂μ := by
  classical
  let b (p : P) : Ω →ᵇ ℂ :=
    actualWilsonObservableBCF (fun ω => U ω p) (words p) (coeff p)
      (actual_wilson_polynomial_continuous (fun ω => U ω p) (hU p) (words p) (coeff p))
  have hint (tuple : Fin r → P) : Integrable (fun ω =>
      ∏ j, weights (tuple j) *
        actualWilsonPolynomial (U ω (tuple j)) (words (tuple j)) (coeff (tuple j))) μ := by
    have he : (((∏ j, weights (tuple j) • b (tuple j)) : Ω →ᵇ ℂ) : Ω → ℂ) = fun ω =>
        ∏ j, weights (tuple j) *
          actualWilsonPolynomial (U ω (tuple j)) (words (tuple j)) (coeff (tuple j)) := by
      funext ω
      simp only [BoundedContinuousFunction.prod_apply, BoundedContinuousFunction.smul_apply,
        smul_eq_mul]
      rfl
    rw [← he]
    exact (∏ j, weights (tuple j) • b (tuple j)).integrable μ
  have hd (tuple : Fin r → P) :
      iteratedFDeriv ℂ r (actualWilsonGeneratingFunction μ weights U words coeff) 0
        (fun j => Pi.single (tuple j) (1 : ℂ)) =
      ∫ ω, ∏ j, weights (tuple j) *
        actualWilsonPolynomial (U ω (tuple j)) (words (tuple j)) (coeff (tuple j)) ∂μ := by
    rw [(actual_wilson_source_derivatives μ weights U words coeff hU).2.2]
    congr 1
    funext ω
    apply Finset.prod_congr rfl
    intro j _
    simp [Pi.single_apply, mul_ite, ite_mul]
  have hterm (tuple : Fin r → P) : Integrable (fun ω =>
      (∏ j, weights (tuple j) *
        actualWilsonPolynomial (U ω (tuple j)) (words (tuple j)) (coeff (tuple j))) *
          f (locations tuple)) μ := (hint tuple).mul_const _
  refine ⟨integrable_finsetSum _ (fun tuple _ => hterm tuple), ?_⟩
  simp only [actualWilsonSourceJointDistribution, sum_apply,
    smul_apply, joint_schwartz_eval_clm_apply, smul_eq_mul]
  simp_rw [hd]
  unfold actualWordJointCutoff
  rw [integral_finsetSum _ (fun tuple _ => hterm tuple)]
  apply Finset.sum_congr rfl
  intro tuple _
  rw [integral_mul_const]

end YMUIC.Original30
