import YMOriginal.Original24_UnmarkedRGGeometry
import YMOriginal.Original24_PhysicalPlacementClosure

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24: U1 actual unmarked R-sector inputs directly into B10

The former abstract source sums used assumptions hweightedOld/hweightedNew.
Here those assumptions are DERIVED from the correct U1-OLD/NEW *unmarked*
activity coefficients:
  ||R_old|| <= CR*g^kappa0*exp(-kappaR*d)
  ||R_new|| <= CRnew*exp(-p0(g))*exp(-kappaR*d),
plus the unchanged native root-distance dictionary
  dRoot <= cRt+cGeo*d.

The U2 rooted-tree counting/summation bounds and B10 fifth-order
Taylor remainder remain explicit *original upstream inputs*.
They are not arbitrary assumptions on the desired marked-R
conclusion.

All source observables are finite ordered SU(2) Wilson-word
polynomials, not independent 21-Gram reconstructed surrogates.
-/

/-- This is the original U1 source activity factor, with no
replacement of a canonical dimensional power by a small coupling. -/
def oldRActivityFactor (g kappa0 CR : ℝ) : ℝ :=
  CR * Real.rpow g kappa0

def newRActivityFactor (g CRnew : ℝ) (p0 : ℝ → ℝ) : ℝ :=
  CRnew * Real.exp (-p0 g)

/-- U1's unmarked old/new R bounds and native geometry produce
the exact ROOT-WEIGHTED two-sector estimates. Neither weighted
marked-R bound nor the desired original24 source-class conclusion
is among the assumptions. -/
theorem actual_U1_old_new_root_weighted
    {Γ : Type*}
    (oldR newR : Γ → ℂ)
    (length : Γ → ℝ)
    (g kappa0 kappaR CR CRnew : ℝ) (p0 : ℝ → ℝ)
    (hg : 0 < g) (hCR : 0 ≤ CR) (hCRnew : 0 ≤ CRnew)
    (mu cGeo cRt dRoot : ℝ) (hmu : 0 ≤ mu)
    (hgeom : ∀ γ, dRoot ≤ cRt + cGeo * length γ)
    (hOld : ∀ γ,
      ‖oldR γ‖ ≤ oldRActivityFactor g kappa0 CR *
        Real.exp (-kappaR * length γ))
    (hNew : ∀ γ,
      ‖newR γ‖ ≤ newRActivityFactor g CRnew p0 *
        Real.exp (-kappaR * length γ)) :
    (∀ γ, Real.exp (mu * dRoot) * ‖oldR γ‖ ≤
      Real.exp (mu * cRt) *
        (oldRActivityFactor g kappa0 CR *
          Real.exp (-(kappaR - mu * cGeo) * length γ))) ∧
    (∀ γ, Real.exp (mu * dRoot) * ‖newR γ‖ ≤
      Real.exp (mu * cRt) *
        (newRActivityFactor g CRnew p0 *
          Real.exp (-(kappaR - mu * cGeo) * length γ))) := by
  have hOldPos : 0 ≤ oldRActivityFactor g kappa0 CR := by
    exact mul_nonneg hCR (Real.rpow_pos_of_pos hg _).le
  have hNewPos : 0 ≤ newRActivityFactor g CRnew p0 := by
    exact mul_nonneg hCRnew (Real.exp_pos _).le
  exact ⟨
    weighted_root_from_unmarked_distance
      oldR length kappaR mu cGeo cRt dRoot
      (oldRActivityFactor g kappa0 CR) hmu hOldPos hgeom hOld,
    weighted_root_from_unmarked_distance
      newR length kappaR mu cGeo cRt dRoot
      (newRActivityFactor g CRnew p0) hmu hNewPos hgeom hNew⟩

/-- THE U1/U2/B10 fixed-D conditional inference with exact actual source
types and physical fourth-order-vs-fifth-order 4D placement ratio.
There is no independently postulated bound on a marked old/new-R
source, and no arbitrary smallness of q.

Still to derive from Yang--Mills: the source roots' canonical
normalization/jet dictionary, the U2 SAME-native-geometry tree-count
estimates, and B10's Taylor estimate on the actual post-R coefficients.
Until then this is a strict conditional assembly, not full Original24.
-/
theorem actual_U1_U2_B10_fixedD_source_tail
    {P T Γ : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (oldR newR : Γ → ℂ) (length : Γ → ℝ)
    (g kappa0 kappaR CR CRnew : ℝ) (p0 : ℝ → ℝ)
    (hg : 0 < g) (hCR : 0 ≤ CR) (hCRnew : 0 ≤ CRnew)
    (mu cGeo cRt dRoot : ℝ) (hmu : 0 ≤ mu)
    (hgeom : ∀ γ, dRoot ≤ cRt + cGeo * length γ)
    (hOld : ∀ γ,
      ‖oldR γ‖ ≤ oldRActivityFactor g kappa0 CR *
        Real.exp (-kappaR * length γ))
    (hNew : ∀ γ,
      ‖newR γ‖ ≤ newRActivityFactor g CRnew p0 *
        Real.exp (-kappaR * length γ))
    (Nroot : ℕ)
    (hTreeOld : Summable (fun γ : Γ =>
      oldRActivityFactor g kappa0 CR *
        Real.exp (-(kappaR-mu*cGeo)*length γ)))
    (hTreeNew : Summable (fun γ : Γ =>
      newRActivityFactor g CRnew p0 *
        Real.exp (-(kappaR-mu*cGeo)*length γ)))
    (hU2Old :
      (∑' γ : Γ, oldRActivityFactor g kappa0 CR *
        Real.exp (-(kappaR-mu*cGeo)*length γ)) ≤
      (Nroot : ℝ) * oldRActivityFactor g kappa0 CR)
    (hU2New :
      (∑' γ : Γ, newRActivityFactor g CRnew p0 *
        Real.exp (-(kappaR-mu*cGeo)*length γ)) ≤
      (Nroot : ℝ) * newRActivityFactor g CRnew p0)
    (L theta : ℝ) (hL : 1 < L)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (remainder : ℕ → ℂ)
    (hB10 : ∀ m, ‖remainder m‖ ≤
      ((∑' γ, ‖actualWordMarkedR U words coeff s oldR γ‖) +
        (∑' γ, ‖actualWordMarkedR U words coeff s newR γ‖)) *
      (L ^ (4 * m) * L ^ (-(5 - theta) * (m : ℝ)))) :
    Summable (fun m => ‖remainder m‖) ∧
      (∑' m, ‖remainder m‖) ≤
      ((2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
          (oldRActivityFactor g kappa0 CR +
            newRActivityFactor g CRnew p0) *
          Real.exp (-mu * dRoot)) /
            (1 - L ^ (-(1 - theta) : ℝ)) := by
  obtain ⟨hWeightedOld, hWeightedNew⟩ :=
    actual_U1_old_new_root_weighted oldR newR length
      g kappa0 kappaR CR CRnew p0 hg hCR hCRnew
      mu cGeo cRt dRoot hmu hgeom hOld hNew
  have hOldPos : 0 ≤ oldRActivityFactor g kappa0 CR := by
    exact mul_nonneg hCR (Real.rpow_pos_of_pos hg _).le
  have hNewPos : 0 ≤ newRActivityFactor g CRnew p0 := by
    exact mul_nonneg hCRnew (Real.exp_pos _).le
  exact actual_word_four_dimensional_post_r_tail U words coeff s hsmall
    oldR newR
    (fun γ => oldRActivityFactor g kappa0 CR *
      Real.exp (-(kappaR-mu*cGeo)*length γ))
    (fun γ => newRActivityFactor g CRnew p0 *
      Real.exp (-(kappaR-mu*cGeo)*length γ))
    mu cRt dRoot
    (oldRActivityFactor g kappa0 CR)
    (newRActivityFactor g CRnew p0)
    Nroot
    (fun γ => mul_nonneg hOldPos (Real.exp_pos _).le)
    (fun γ => mul_nonneg hNewPos (Real.exp_pos _).le)
    hWeightedOld hWeightedNew hTreeOld hTreeNew hU2Old hU2New
    L theta hL htheta0 htheta1 remainder hB10

end YMUIC.Original24
