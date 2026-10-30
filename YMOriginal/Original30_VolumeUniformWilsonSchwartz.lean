import YMOriginal.Original30_SpatialLatticeGeometry
import YMOriginal.Original30_ActualWordSmearing

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# Physical 4D lattice Wilson source: UV AND infinite-volume uniform

This module combines:
(a) actual a*Z^4 Euclidean site locations, with a>0,
(b) a^4 source volume weights,
(c) true ordered SU2 Wilson-word polynomial observables,
(d) full-space Schwartz seminorm p_(0,0)+p_(8,0), and
(e) the already strictly verified spatial cubature <=96.

It derives a bound independent of both UV spacing a and the physical
box length N*a, WITHOUT a model-side cubature hypothesis.

The finite template budget K is explicit and must still be proved
uniform for actual RG-renormalized a^-d source coefficients. This
is a result on actual BARE Wilson words, not yet the full C29
renormalized fixed-D local curvature source.
-/

/-- Exact tensor-product reciprocal-square lattice site weight. -/
theorem true_site_cubature_weight_identity
    {N : ℕ} (a : ℝ) (site : Fin 4 → Fin N) :
    latticeFourDimWeight a site =
      a ^ 4 / (∏ i : Fin 4, (1 + a * (site i : ℝ)) ^ 2) := by
  unfold latticeFourDimWeight latticeOneDimWeight
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Pointwise actual 4D grid Schwartz decay pays exactly for spatial
infinite-volume summability at the cost of a fixed 8th-order weight. -/
theorem actual_site_schwartz_cubature_point
    {N : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (site : Fin 4 → Fin N) (f : SchwartzMap Space4 ℂ) :
    a ^ 4 * ‖f (trueLatticeSitePosition a site)‖ ≤
      128 *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ 8 0 f) *
        latticeFourDimWeight a site := by
  let x : Space4 := trueLatticeSitePosition a site
  let D : ℝ := ∏ i : Fin 4, (1 + a * (site i : ℝ)) ^ 2
  let P : ℝ :=
    SchwartzMap.seminorm ℂ 0 0 f +
      SchwartzMap.seminorm ℂ 8 0 f
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i hi
    positivity
  have hP : 0 ≤ P :=
    add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hgeom : D ≤ 128 * (1 + ‖x‖ ^ 8) :=
    true_site_product_weight_le_schwartz a ha site
  have hsch :
      (1 + ‖x‖ ^ 8) * ‖f x‖ ≤ P :=
    schwartz_weighted_point_bound 8 f x
  have hmul : ‖f x‖ * D ≤ 128 * P := by
    calc
      ‖f x‖ * D = D * ‖f x‖ := by ring
      _ ≤ (128 * (1 + ‖x‖ ^ 8)) * ‖f x‖ :=
        mul_le_mul_of_nonneg_right hgeom (norm_nonneg _)
      _ = 128 * ((1 + ‖x‖ ^ 8) * ‖f x‖) := by ring
      _ ≤ 128 * P :=
        mul_le_mul_of_nonneg_left hsch (by norm_num)
  have hf : ‖f x‖ ≤ 128 * P / D :=
    (le_div_iff₀ hD).mpr hmul
  have heq :
      latticeFourDimWeight a site = a ^ 4 / D :=
    true_site_cubature_weight_identity a site
  calc
    a ^ 4 * ‖f (trueLatticeSitePosition a site)‖ =
      a ^ 4 * ‖f x‖ := rfl
    _ ≤ a ^ 4 * (128 * P / D) :=
      mul_le_mul_of_nonneg_left hf (pow_nonneg ha 4)
    _ = 128 * P * (a ^ 4 / D) := by ring
    _ = 128 *
      (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ 8 0 f) *
        latticeFourDimWeight a site := by rw [heq]

/-- Actual six positive plaquette orientations at each physical 4D
lattice site, retaining the site coordinate rather than an opaque
Fin (N^4) encoding. -/
abbrev TrueSpatialPlaquettes (N : ℕ) :=
  Fin 6 × (Fin 4 → Fin N)

/-- Real bare Wilson source with actual a^4 quadrature and actual
4D coordinates, arbitrary finite ordered SU2 word templates. -/
def actualSpatialWilsonSmearing
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (f : SchwartzMap Space4 ℂ) : ℂ :=
  ∑ p : TrueSpatialPlaquettes N,
    ((a ^ 4 : ℝ) : ℂ) *
      (f (trueLatticeSitePosition a p.2) *
        actualWilsonPolynomial (U p) (words p) (coeff p))

/-- TRUE UNBOUNDED PHYSICAL VOLUME result, independent of both
N and a: total source ≤ 12288 K (p_(0,0)+p_(8,0)).
The physical K is the actual fixed-complexity bare Wilson template
coefficient budget; it is not a renormalized RG norm guarantee. -/
theorem actual_spatial_wilson_uniform_unbounded_box
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : SchwartzMap Space4 ℂ) :
    ‖actualSpatialWilsonSmearing N a U words coeff f‖ ≤
      12288 * K *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ 8 0 f) := by
  let P : ℝ := SchwartzMap.seminorm ℂ 0 0 f +
      SchwartzMap.seminorm ℂ 8 0 f
  have hP : 0 ≤ P :=
    add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hweight (p : TrueSpatialPlaquettes N) :
      0 ≤ latticeFourDimWeight a p.2 := by
    unfold latticeFourDimWeight
    apply Finset.prod_nonneg
    intro i hi
    exact lattice_one_dim_weight_nonneg a ha.le _
  have hsingle (p : TrueSpatialPlaquettes N) :
      ‖((a ^ 4 : ℝ) : ℂ) *
        (f (trueLatticeSitePosition a p.2) *
          actualWilsonPolynomial (U p) (words p) (coeff p))‖ ≤
      (128 * K * P) * latticeFourDimWeight a p.2 := by
    have hf := actual_site_schwartz_cubature_point
      a ha.le p.2 f
    have hO :
        ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ ≤ K :=
      (actual_wilson_polynomial_bound (U p) (words p) (coeff p)).trans
        (hbudget p)
    have hleft :
        a ^ 4 * ‖f (trueLatticeSitePosition a p.2)‖ ≤
          128 * P * latticeFourDimWeight a p.2 := hf
    have hbound :
        (a ^ 4 * ‖f (trueLatticeSitePosition a p.2)‖) *
          ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ ≤
        (128 * P * latticeFourDimWeight a p.2) * K :=
      mul_le_mul hleft hO
        (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hP) (hweight p))
    calc
      ‖((a ^ 4 : ℝ) : ℂ) *
        (f (trueLatticeSitePosition a p.2) *
          actualWilsonPolynomial (U p) (words p) (coeff p))‖ =
        (a ^ 4 * ‖f (trueLatticeSitePosition a p.2)‖) *
          ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg ha.le 4)]
            ring
      _ ≤ (128 * P * latticeFourDimWeight a p.2) * K :=
        hbound
      _ = (128 * K * P) * latticeFourDimWeight a p.2 := by ring
  have hsum := lattice_plaquette_four_dimensional_uniform
    a ha ha1 N
  calc
    ‖actualSpatialWilsonSmearing N a U words coeff f‖ ≤
      ∑ p : TrueSpatialPlaquettes N,
        ‖((a ^ 4 : ℝ) : ℂ) *
          (f (trueLatticeSitePosition a p.2) *
            actualWilsonPolynomial (U p) (words p) (coeff p))‖ :=
            norm_sum_le _ _
    _ ≤ ∑ p : TrueSpatialPlaquettes N,
        (128 * K * P) * latticeFourDimWeight a p.2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hsingle p
    _ = (128 * K * P) *
          (∑ p : TrueSpatialPlaquettes N,
            latticeFourDimWeight a p.2) := by
            rw [Finset.mul_sum]
    _ ≤ (128 * K * P) * 96 :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (mul_nonneg (by norm_num) hK) hP)
    _ = 12288 * K *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ 8 0 f) := by
          dsimp [P]
          ring

end YMUIC.Original30
