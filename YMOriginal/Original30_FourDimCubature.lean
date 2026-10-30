import YMOriginal.Original30_OneDimCubature
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30

/-!
# Actual FOUR-dimensional lattice spatial cubature without box-volume loss

At each 4D lattice site x=a*n, with n_i in 0,..,N-1, define
  w_a(n) = Product_{i=1..4} a/(1+a*n_i)^2.
The 1D telescoping estimate gives sum_n w_a(n) <= 2^4 = 16
for all 0<a<=1 and all N, hence also
  sum_{plaquettes p} w_a(site(p)) <= 6*16 = 96.

This is an actual four-dimensional lattice estimate, independent of
both the ultraviolet spacing and the *physical box length* N*a.
It is the needed geometric replacement for the previous 6*R^4
cubature bound in the Schwartz-weighted Original30 source estimates.
The exact test-function product-weight dominance and true
a^-d source coefficient normalization remain distinct obligations.
-/

/-- The exact normalized one-dimensional spatial weight. -/
def latticeOneDimWeight (a : ℝ) {N : ℕ} (k : Fin N) : ℝ :=
  a / (1 + a * (k : ℝ)) ^ 2

theorem lattice_one_dim_weight_nonneg
    (a : ℝ) (ha : 0 ≤ a) {N : ℕ} (k : Fin N) :
    0 ≤ latticeOneDimWeight a k := by
  unfold latticeOneDimWeight
  positivity

/-- Product of four physical lattice tails at a true 4D site. -/
def latticeFourDimWeight (a : ℝ) {N : ℕ}
    (site : Fin 4 → Fin N) : ℝ :=
  ∏ i : Fin 4, latticeOneDimWeight a (site i)

/-- The exact 4D spatial cubature factor remains bounded by 16,
even as N*a tends to infinity (0<a<=1). -/
theorem lattice_four_dimensional_uniform_all_cutoffs
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    (∑ site : Fin 4 → Fin N,
      latticeFourDimWeight a site) ≤ 16 := by
  let w : Fin N → ℝ := latticeOneDimWeight a
  have hsum1 : (∑ k : Fin N, w k) ≤ 2 := by
    simpa only [w, latticeOneDimWeight, ← Fin.sum_univ_eq_sum_range] using
      lattice_inverse_square_uniform_all_cutoffs a ha ha1 N
  have hsum0 : 0 ≤ ∑ k : Fin N, w k := by
    apply Finset.sum_nonneg
    intro k hk
    exact lattice_one_dim_weight_nonneg a ha.le k
  have hpi :
      (∑ site : Fin 4 → Fin N, ∏ i : Fin 4, w (site i)) =
        (∑ k : Fin N, w k) ^ 4 := by
    have h := Finset.sum_pow'
      (Finset.univ : Finset (Fin N)) w 4
    simpa only [Fintype.piFinset_univ] using h.symm
  change (∑ site : Fin 4 → Fin N,
      ∏ i : Fin 4, w (site i)) ≤ 16
  rw [hpi]
  have hfour := pow_le_pow_left₀ hsum0 hsum1 4
  norm_num at hfour
  exact hfour

/-- Six positive plaquette directions times a 4D lattice family.
The 96 constant is independent of N and physical volume N*a. -/
theorem lattice_plaquette_four_dimensional_uniform
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    (∑ p : Fin 6 × (Fin 4 → Fin N),
      latticeFourDimWeight a p.2) ≤ 96 := by
  have h4 := lattice_four_dimensional_uniform_all_cutoffs
    a ha ha1 N
  calc
    (∑ p : Fin 6 × (Fin 4 → Fin N),
        latticeFourDimWeight a p.2) =
      ∑ o : Fin 6, ∑ site : Fin 4 → Fin N,
        latticeFourDimWeight a site := by
          simp only [Fintype.sum_prod_type]
    _ = 6 * (∑ site : Fin 4 → Fin N,
          latticeFourDimWeight a site) := by simp
    _ ≤ 6 * 16 :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 96 := by norm_num

end YMUIC.Original30
