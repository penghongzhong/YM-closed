import YMOriginal.Original30_JointLatticeSchwartz
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03
open MeasureTheory

/-!
# Genuine finite-volume SU2 Wilson probability-measure joint source

For ANY probability measure on actual SU2 link configurations, with
the usual measurability input, integrate the true finite lattice joint
4r-variable Wilson source (not a surrogate deterministic moment). The
uniform absolute bound follows from the already certified SU2
polynomial root norms and from the 6*N^4 physical a^4 cubature, and
NOT from any assumed moment or factorial growth.

Fixed finite physical R is essential; no claim of volume-uniform
R->infinity or of nontrivial renormalized curvature scaling is made.
-/

/-- Actual regulated expectation of a joint 4r-dimensional SU2 Wilson
source under an arbitrary probability measure. All r-point moments
are integrable and satisfy the finite-box cutoff-independent bound. -/
theorem actual_word_joint_probability_integrable_and_bound
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config) [IsProbabilityMeasure μ]
    (r N : ℕ) (a R : ℝ)
    (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hbox : (N : ℝ) * a ≤ R)
    (U : Config → WilsonBoxPlaquettes N → W → SU2)
    (words : WilsonBoxPlaquettes N → T → List (List W))
    (coeff : WilsonBoxPlaquettes N → T → ℂ)
    (positions : (Fin r → WilsonBoxPlaquettes N) →
      EuclideanSpace ℝ (Fin (4 * r)))
    (f : YMUIC.Original34.JointTest r)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (hMeas : AEStronglyMeasurable
      (fun ω : Config =>
        actualWordJointCutoff r
          (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
          (U ω) words coeff positions f) μ) :
    Integrable (fun ω : Config =>
      actualWordJointCutoff r
        (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff positions f) μ ∧
    ‖∫ ω : Config, actualWordJointCutoff r
        (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff positions f ∂μ‖ ≤
      (6 * K * R ^ 4) ^ r *
        SchwartzMap.seminorm ℂ 0 0 f := by
  have hnorm (ω : Config) :
      ‖actualWordJointCutoff r
        (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff positions f‖ ≤
      (6 * K * R ^ 4) ^ r *
        SchwartzMap.seminorm ℂ 0 0 f :=
    actual_word_joint_physical_box_bound r N a R ha hR hbox
      (U ω) words coeff positions f K hK hbudget
  have hint : Integrable (fun ω : Config =>
      actualWordJointCutoff r
        (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff positions f) μ :=
    Integrable.of_bound hMeas
      ((6 * K * R ^ 4) ^ r *
        SchwartzMap.seminorm ℂ 0 0 f)
      (Filter.Eventually.of_forall hnorm)
  refine ⟨hint, ?_⟩
  have hprob : μ.real Set.univ = 1 := by simp
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall hnorm)
  simpa only [hprob, mul_one] using hb

end YMUIC.Original30
