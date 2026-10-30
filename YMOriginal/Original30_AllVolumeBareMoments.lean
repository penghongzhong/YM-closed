import YMOriginal.Original30_VolumeUniformWilsonSchwartz
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03
open MeasureTheory

/-!
# All-r SU2 bare Wilson mixed moments, physical volume and cutoff uniform

This is the genuine joint-order multilinear BARE Wilson source estimate
on f_1,...,f_r in Schwartz(R4), with the SAME four-dimensional lattice
configuration U in all r slots. There is no independence hypothesis,
factorization of the probability law, or assumption on cumulant sizes.

For every 0<a<=1 and every N (including N*a->infinity),

 |Product_j (sum_p a^4 f_j(x_p) O_p(U))|
       <= (12288*K)^r Product_j [p_(0,0)(f_j)+p_(8,0)(f_j)].

For an arbitrary probability measure on the lattice SU2
configurations, the same bound holds for its genuine r-point moment
after integration. This proves the C29 (345)-shaped PURE-TENSOR
factorial growth for bounded bare Wilson loops and any volume.

It does not establish the canonical a^(-d) curvature normalization,
rooted RG derivative dictionary or projective tensor extension to a
single joint 4r-variable test. Nor does it establish a physical
continuum same-net limit. These are the Original30 blockers.
-/

/-- True joint-order bare Wilson product for the SAME configuration,
not a product of independent expectations. -/
def actualBareWilsonMixedMoment
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a : ℝ)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (f : Fin r → SchwartzMap Space4 ℂ) : ℂ :=
  ∏ j : Fin r,
    actualSpatialWilsonSmearing N a U words coeff (f j)

/-- Cutoff/volume-uniform multilinear order-r estimate derived directly
from true 4D site cubature and SU2 polynomial source amplitudes. -/
theorem actual_bare_wilson_all_order_uniform
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : Fin r → SchwartzMap Space4 ℂ) :
    ‖actualBareWilsonMixedMoment r N a U words coeff f‖ ≤
      (12288 * K) ^ r *
        (∏ j : Fin r,
          (SchwartzMap.seminorm ℂ 0 0 (f j) +
            SchwartzMap.seminorm ℂ 8 0 (f j))) := by
  let B : ℝ := 12288 * K
  let P : Fin r → ℝ := fun j =>
    SchwartzMap.seminorm ℂ 0 0 (f j) +
      SchwartzMap.seminorm ℂ 8 0 (f j)
  have hBound (j : Fin r) :
      ‖actualSpatialWilsonSmearing N a U words coeff (f j)‖ ≤
        B * P j := by
    exact actual_spatial_wilson_uniform_unbounded_box
      N a ha ha1 U words coeff K hK hbudget (f j)
  calc
    ‖actualBareWilsonMixedMoment r N a U words coeff f‖ =
      ∏ j : Fin r,
        ‖actualSpatialWilsonSmearing N a U words coeff (f j)‖ := by
          exact norm_prod _ _
    _ ≤ ∏ j : Fin r, B * P j := by
          exact Finset.prod_le_prod₀
            (fun j hj => norm_nonneg _)
            (fun j hj => hBound j)
    _ = B ^ r * (∏ j : Fin r, P j) := by
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = (12288 * K) ^ r *
          (∏ j : Fin r,
            (SchwartzMap.seminorm ℂ 0 0 (f j) +
              SchwartzMap.seminorm ℂ 8 0 (f j))) := rfl

/-- Genuine bare Wilson r-point expectation under a probability
measure, no independence or Gaussianity assumption on SU2 links.
The measurability hypothesis concerns the EXACT lattice observable,
not any growth estimate, and actual Wilson probability laws satisfy
it when coordinate maps are measurable. -/
theorem actual_bare_wilson_probability_all_order
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : Measure Config) [IsProbabilityMeasure μ]
    (r N : ℕ) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : Fin r → SchwartzMap Space4 ℂ)
    (hMeas : AEStronglyMeasurable (fun ω : Config =>
      actualBareWilsonMixedMoment r N a (U ω) words coeff f) μ) :
    Integrable (fun ω : Config =>
      actualBareWilsonMixedMoment r N a (U ω) words coeff f) μ ∧
    ‖∫ ω : Config,
      actualBareWilsonMixedMoment r N a (U ω) words coeff f ∂μ‖ ≤
      (12288 * K) ^ r *
        (∏ j : Fin r,
          (SchwartzMap.seminorm ℂ 0 0 (f j) +
            SchwartzMap.seminorm ℂ 8 0 (f j))) := by
  let M : ℝ :=
    (12288 * K) ^ r *
        (∏ j : Fin r,
          (SchwartzMap.seminorm ℂ 0 0 (f j) +
            SchwartzMap.seminorm ℂ 8 0 (f j)))
  have hbound (ω : Config) :
      ‖actualBareWilsonMixedMoment r N a
        (U ω) words coeff f‖ ≤ M :=
    actual_bare_wilson_all_order_uniform
      r N a ha ha1 (U ω) words coeff K hK hbudget f
  have hInt : Integrable (fun ω : Config =>
      actualBareWilsonMixedMoment r N a (U ω) words coeff f) μ :=
    Integrable.of_bound hMeas M (Filter.Eventually.of_forall hbound)
  refine ⟨hInt, ?_⟩
  have hprob : μ.real Set.univ = 1 := by simp
  have hmean := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall hbound)
  simpa only [M, hprob, mul_one] using hmean

end YMUIC.Original30
