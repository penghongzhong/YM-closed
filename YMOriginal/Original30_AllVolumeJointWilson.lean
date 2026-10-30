import YMOriginal.Original30_JointProductSchwartzDecay
import YMOriginal.Original30_JointLatticeSchwartz

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# Genuine SU(2) Wilson joint 4r Schwartz growth, all UV/volume cutoffs

The physical a^4-weighted source and genuine ordered SU(2) word
polynomials are evaluated on the SAME lattice configuration in every
field slot. Unlike the earlier fixed-box argument, a true 4D spatial
cubature pays the infinite-volume sum uniformly, while the joint
Schwartz seminorm of order 8r pays all r lattice distances at once.

The sole geometry premise specifies that the joint 4r spacetime point
dominates the norm of every component site; for the canonical
concatenated site location this is an elementary isometric coordinate
identity, left to a separate Lean module.

This is a bare-source result, NOT a proof of the physical canonically
renormalized YM curvature source or same-net continuum limit.
-/

/-- Exact sitewise coefficient bound with the genuine inverse-square
four-dimensional lattice weight. -/
theorem actual_wilson_site_weighted_coefficient_bound
    {W T : Type*} [Fintype T]
    (N : ℕ) (a : ℝ) (ha : 0 < a)
    (p : TrueSpatialPlaquettes N)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : actualWilsonPolynomialBudget (words p) (coeff p) ≤ K) :
    ‖((a ^ 4 : ℝ) : ℂ) *
       actualWilsonPolynomial (U p) (words p) (coeff p)‖ ≤
      (128 * K) *
        (1 + ‖trueLatticeSitePosition a p.2‖ ^ 8) *
        latticeFourDimWeight a p.2 := by
  let x : Space4 := trueLatticeSitePosition a p.2
  let D : ℝ := ∏ i : Fin 4, (1 + a * (p.2 i : ℝ)) ^ 2
  let w : ℝ := latticeFourDimWeight a p.2
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i hi
    positivity
  have hw : 0 ≤ w := by
    dsimp [w, latticeFourDimWeight]
    apply Finset.prod_nonneg
    intro i hi
    exact lattice_one_dim_weight_nonneg a ha.le _
  have hwdict : w = a ^ 4 / D := by
    dsimp [w, D]
    exact true_site_cubature_weight_identity a p.2
  have hvolume : a ^ 4 = D * w := by
    rw [hwdict]
    field_simp [hD.ne']
  have hDgeom : D ≤ 128 * (1 + ‖x‖ ^ 8) :=
    true_site_product_weight_le_schwartz a ha.le p.2
  have hspace : a ^ 4 ≤
      (128 * (1 + ‖x‖ ^ 8)) * w := by
    calc
      a ^ 4 = D * w := hvolume
      _ ≤ 128 * (1 + ‖x‖ ^ 8) * w :=
        mul_le_mul_of_nonneg_right hDgeom hw
  have hO : ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ ≤ K :=
    (actual_wilson_polynomial_bound (U p) (words p) (coeff p)).trans
      hbudget
  calc
    ‖((a ^ 4 : ℝ) : ℂ) *
       actualWilsonPolynomial (U p) (words p) (coeff p)‖ =
        a ^ 4 *
          ‖actualWilsonPolynomial (U p) (words p) (coeff p)‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg ha.le _)]
    _ ≤ (128 * (1 + ‖x‖ ^ 8) * w) * K :=
      mul_le_mul hspace hO (norm_nonneg _)
        (mul_nonneg (by positivity) hw)
    _ = (128 * K) * (1 + ‖trueLatticeSitePosition a p.2‖ ^ 8) *
          latticeFourDimWeight a p.2 := by
      dsimp [x, w]
      ring

/-- Actual full JOINT 4r-dimensional Schwartz source, uniform for every
lattice spacing 0<a<=1, every cutoff N and physical volume N*a.
The test F is NOT required to be a product of single-field tests.

The hgeom premise is a source-location compatibility identity rather
than a source norm/analytic growth assumption. -/
theorem actual_joint_bare_wilson_all_volume_bound
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (locations : (Fin r → TrueSpatialPlaquettes N) →
       EuclideanSpace ℝ (Fin (4 * r)))
    (hgeom : ∀ tuple : Fin r → TrueSpatialPlaquettes N,
      ∀ j : Fin r,
        ‖trueLatticeSitePosition a (tuple j).2‖ ≤
          ‖locations tuple‖)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualWordJointCutoff r
      (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff locations f‖ ≤
      (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  classical
  let P : ℝ :=
    SchwartzMap.seminorm ℂ 0 0 f +
      SchwartzMap.seminorm ℂ (8 * r) 0 f
  let w : TrueSpatialPlaquettes N → ℝ :=
    fun p => latticeFourDimWeight a p.2
  have hP : 0 ≤ P := by
    dsimp [P]
    exact add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hw (p : TrueSpatialPlaquettes N) : 0 ≤ w p := by
    dsimp [w, latticeFourDimWeight]
    apply Finset.prod_nonneg
    intro i hi
    exact lattice_one_dim_weight_nonneg a ha.le _
  have hProd (tuple : Fin r → TrueSpatialPlaquettes N) :
      ‖∏ j : Fin r,
        ((a ^ 4 : ℝ) : ℂ) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))‖ ≤
      (128 * K) ^ r *
        (∏ j : Fin r,
          (1 + ‖trueLatticeSitePosition a (tuple j).2‖ ^ 8)) *
        (∏ j : Fin r, w (tuple j)) := by
    rw [norm_prod]
    calc
      (∏ j : Fin r,
        ‖((a ^ 4 : ℝ) : ℂ) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))‖) ≤
        ∏ j : Fin r,
          (128 * K) *
            (1 + ‖trueLatticeSitePosition a (tuple j).2‖ ^ 8) *
            w (tuple j) := by
              apply Finset.prod_le_prod₀
              · intro j hj
                exact norm_nonneg _
              · intro j hj
                exact actual_wilson_site_weighted_coefficient_bound
                  N a ha (tuple j) U words coeff K hK (hbudget (tuple j))
      _ = (128 * K) ^ r *
          (∏ j : Fin r,
            (1 + ‖trueLatticeSitePosition a (tuple j).2‖ ^ 8)) *
          (∏ j : Fin r, w (tuple j)) := by
            simp only [Finset.prod_mul_distrib, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
            ring
  have hTerm (tuple : Fin r → TrueSpatialPlaquettes N) :
      ‖(∏ j : Fin r,
        ((a ^ 4 : ℝ) : ℂ) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))) *
        f (locations tuple)‖ ≤
      (256 * K) ^ r * P * (∏ j : Fin r, w (tuple j)) := by
    have hwp : 0 ≤ (∏ j : Fin r, w (tuple j)) :=
      Finset.prod_nonneg (fun j hj => hw (tuple j))
    have hpow : 0 ≤ (128 * K) ^ r := by positivity
    have hSchw :=
      joint_schwartz_pays_product_spatial_weights
        r (fun j => trueLatticeSitePosition a (tuple j).2)
        (locations tuple) (hgeom tuple) f
    have hsp : (128 * K) ^ r * (2 : ℝ) ^ r =
        (256 * K) ^ r := by
      rw [← mul_pow]
      congr 1
      ring
    rw [norm_mul]
    calc
      ‖∏ j : Fin r,
        ((a ^ 4 : ℝ) : ℂ) *
          actualWilsonPolynomial (U (tuple j))
            (words (tuple j)) (coeff (tuple j))‖ *
            ‖f (locations tuple)‖ ≤
          ((128 * K) ^ r *
            (∏ j : Fin r,
              (1 + ‖trueLatticeSitePosition a (tuple j).2‖ ^ 8)) *
            (∏ j : Fin r, w (tuple j))) * ‖f (locations tuple)‖ :=
        mul_le_mul_of_nonneg_right (hProd tuple) (norm_nonneg _)
      _ = (128 * K) ^ r *
          ((∏ j : Fin r,
            (1 + ‖trueLatticeSitePosition a (tuple j).2‖ ^ 8)) *
            ‖f (locations tuple)‖) *
          (∏ j : Fin r, w (tuple j)) := by ring
      _ ≤ (128 * K) ^ r * ((2 : ℝ) ^ r * P) *
          (∏ j : Fin r, w (tuple j)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by simpa only [P] using hSchw) hpow)
          hwp
      _ = (256 * K) ^ r * P *
          (∏ j : Fin r, w (tuple j)) := by
        rw [← hsp]
        ring
  have hweightSum :
      (∑ p : TrueSpatialPlaquettes N, w p) ≤ 96 :=
    lattice_plaquette_four_dimensional_uniform a ha ha1 N
  have hweightNonneg :
      0 ≤ ∑ p : TrueSpatialPlaquettes N, w p :=
    Finset.sum_nonneg (fun p hp => hw p)
  have hsumProd :
      (∑ tuple : Fin r → TrueSpatialPlaquettes N,
        ∏ j : Fin r, w (tuple j)) =
        (∑ p : TrueSpatialPlaquettes N, w p) ^ r := by
    have h := Finset.sum_pow'
      (Finset.univ : Finset (TrueSpatialPlaquettes N)) w r
    simpa only [Fintype.piFinset_univ] using h.symm
  have hsum96 :
      (∑ tuple : Fin r → TrueSpatialPlaquettes N,
        ∏ j : Fin r, w (tuple j)) ≤ 96 ^ r := by
    rw [hsumProd]
    exact pow_le_pow_left₀ hweightNonneg hweightSum r
  change ‖actualWordJointCutoff r
    (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U words coeff locations f‖ ≤ (24576 * K) ^ r * P
  calc
    ‖actualWordJointCutoff r
      (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff locations f‖ ≤
      ∑ tuple : Fin r → TrueSpatialPlaquettes N,
        ‖(∏ j : Fin r,
          ((a ^ 4 : ℝ) : ℂ) *
            actualWilsonPolynomial (U (tuple j))
              (words (tuple j)) (coeff (tuple j))) *
          f (locations tuple)‖ := norm_sum_le _ _
    _ ≤ ∑ tuple : Fin r → TrueSpatialPlaquettes N,
          (256 * K) ^ r * P * (∏ j : Fin r, w (tuple j)) :=
      Finset.sum_le_sum (fun tuple _ => hTerm tuple)
    _ = (256 * K) ^ r * P *
        (∑ tuple : Fin r → TrueSpatialPlaquettes N,
          ∏ j : Fin r, w (tuple j)) := by
      rw [Finset.mul_sum]
    _ ≤ (256 * K) ^ r * P * 96 ^ r :=
      mul_le_mul_of_nonneg_left hsum96 (by positivity)
    _ = (24576 * K) ^ r * P := by
      rw [← mul_pow]
      ring

end YMUIC.Original30
