import YMOriginal.Original30_FourDimCubature
import YM.Wilson.WeightedSmearing

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson

/-!
# Exact 4D lattice-location Schwartz weight dictionary

For x_n=a*n in the genuine 4D Euclidean lattice and 0<a<=1,
the following polynomial-weight dominance is proved, not passed as
an abstract geometric hypothesis:

  Product_{i=1}^4 (1+a*n_i)^2 <= 128*(1+||x_n||^8).

This is the missing geometric link from a genuinely 4D Euclidean
Schwartz seminorm to the previously compiled <=96 physical spatial
cubature without fixed physical box radius.
-/

def trueLatticeSitePosition {N : ℕ} (a : ℝ)
    (site : Fin 4 → Fin N) : Space4 :=
  WithLp.toLp 2 (fun i : Fin 4 => a * (site i : ℝ))

/-- Actual coordinate a*n_i is bounded by its full Euclidean norm. -/
theorem true_site_coordinate_le_norm
    {N : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (site : Fin 4 → Fin N) (i : Fin 4) :
    a * (site i : ℝ) ≤ ‖trueLatticeSitePosition a site‖ := by
  have hx : 0 ≤ a * (site i : ℝ) :=
    mul_nonneg ha (by positivity)
  have h := lp.norm_apply_le_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (trueLatticeSitePosition a site) i
  change ‖a * (site i : ℝ)‖ ≤ ‖trueLatticeSitePosition a site‖ at h
  rwa [Real.norm_eq_abs, abs_of_nonneg hx] at h

/-- Elementary polynomial-weight estimate with a dimension-independent
explicit exponent, avoiding noncomputable geometric bounds. -/
theorem one_add_pow_eight_le
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ 8 ≤ 128 * (1 + t ^ 8) := by
  have htwo (u : ℝ) : (1 + u) ^ 2 ≤ 2 * (1 + u ^ 2) := by
    nlinarith [sq_nonneg (u - 1)]
  have hfour : (1 + t) ^ 4 ≤ 8 * (1 + t ^ 4) := by
    calc
      (1 + t) ^ 4 = ((1 + t) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + t ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) (htwo t) 2
      _ = 4 * (1 + t ^ 2) ^ 2 := by ring
      _ ≤ 4 * (2 * (1 + (t ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left (htwo (t ^ 2)) (by norm_num)
      _ = 8 * (1 + t ^ 4) := by ring
  calc
    (1 + t) ^ 8 = ((1 + t) ^ 4) ^ 2 := by ring
    _ ≤ (8 * (1 + t ^ 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfour 2
    _ = 64 * (1 + t ^ 4) ^ 2 := by ring
    _ ≤ 64 * (2 * (1 + (t ^ 4) ^ 2)) :=
      mul_le_mul_of_nonneg_left (htwo (t ^ 4)) (by norm_num)
    _ = 128 * (1 + t ^ 8) := by ring

/-- The EXACT site denominator of the tensor-product inverse-square
weight is controlled by the actual Euclidean position of that site.
No orientation, volume or cutoff constants occur. -/
theorem true_site_product_weight_le_schwartz
    {N : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (site : Fin 4 → Fin N) :
    (∏ i : Fin 4, (1 + a * (site i : ℝ)) ^ 2) ≤
      128 * (1 + ‖trueLatticeSitePosition a site‖ ^ 8) := by
  let x : Space4 := trueLatticeSitePosition a site
  have hprod :
      (∏ i : Fin 4, (1 + a * (site i : ℝ)) ^ 2) ≤
        ∏ _i : Fin 4, (1 + ‖x‖) ^ 2 := by
    apply Finset.prod_le_prod
    intro i hi
    exact pow_le_pow_left₀
      (by positivity : 0 ≤ 1 + a * (site i : ℝ))
      (by
        have h := true_site_coordinate_le_norm a ha site i
        linarith)
      2
  calc
    (∏ i : Fin 4, (1 + a * (site i : ℝ)) ^ 2) ≤
      ∏ _i : Fin 4, (1 + ‖x‖) ^ 2 := hprod
    _ = (1 + ‖x‖) ^ 8 := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ ≤ 128 * (1 + ‖x‖ ^ 8) :=
      one_add_pow_eight_le ‖x‖ (norm_nonneg _)

end YMUIC.Original30
