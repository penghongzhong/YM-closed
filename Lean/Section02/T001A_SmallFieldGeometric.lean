import Mathlib

set_option autoImplicit false

/-!
Internal arithmetic certificates for v133 equations
`sf-polymer-count` -> `sf-rootnorm-derivation`.

The finite-shell combinatorial counting itself will be formalized next.
This file certifies the load-bearing scalar identities:
  δ_sf = κ_pub - κ_sf - c_pol > 0,
  0 < exp(-δ_sf) < 1,
  sum_m exp(-δ_sf)^m = (1-exp(-δ_sf))^{-1}.
-/

namespace YMUICV128.Section02

def sfDelta (kappaPub kappaSf cPol : ℝ) : ℝ :=
  kappaPub - kappaSf - cPol

theorem sfDelta_pos
    {kappaPub kappaSf cPol : ℝ}
    (hsep : kappaSf + cPol < kappaPub) :
    0 < sfDelta kappaPub kappaSf cPol := by
  unfold sfDelta
  linarith

theorem exp_neg_sfDelta_lt_one
    {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-δ) < 1 := by
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)

theorem one_sub_exp_neg_sfDelta_pos
    {δ : ℝ} (hδ : 0 < δ) :
    0 < 1 - Real.exp (-δ) := by
  exact sub_pos.mpr (exp_neg_sfDelta_lt_one hδ)

theorem sf_geometric_tsum
    {δ : ℝ} (hδ : 0 < δ) :
    (∑' m : ℕ, (Real.exp (-δ)) ^ m)
      = (1 - Real.exp (-δ))⁻¹ := by
  exact tsum_geometric_of_lt_one
    (Real.exp_pos (-δ)).le
    (exp_neg_sfDelta_lt_one hδ)

#print axioms sfDelta_pos
#print axioms exp_neg_sfDelta_lt_one
#print axioms one_sub_exp_neg_sfDelta_pos
#print axioms sf_geometric_tsum

end YMUICV128.Section02
