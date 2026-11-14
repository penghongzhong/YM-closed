import YMOriginal.Original24_TwoRootFullRadius

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# C29 source-class repaired: actual 2-root old/new-R histories

This simultaneously yields C29 (317)--(319) for real SU2 Wilson-word
polynomial pairs at arbitrary fixed source radius. The bulk history
coefficients are unchanged and satisfy the ORIGINAL U1 old/new-R
norms; their weighted rooted norms follow from the original native
distance dictionary and U2 rooted-tree estimates.

NO source deformed CMP119/122 bulk R-operation or bound on it is
assumed. The physical graph/history dictionary and model U2 total
count still require checking, so this is not by itself the full
unconditional Original24 manuscript environment.
-/

/-- Exact two-root general bounded-source old/new-R theorem: old-R
amplitude CR*g^kappa0, new-R CRnew*exp(-p0(g)), with the full
non-small fixed radius source factors exp(radius*B)-1. -/
theorem actual_two_root_old_new_r_full_radius
    {P T S Γ : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
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
      (Nroot : ℝ) * newRActivityFactor g CRnew p0) :
    (∑' γ, ‖actualTwoRootMarkedR U wp cp wq cq s t oldR γ‖) ≤
        ((Real.exp (radius * Bp) - 1) *
          (Real.exp (radius * Bq) - 1)) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
        oldRActivityFactor g kappa0 CR * Real.exp (-mu * dRoot) ∧
    (∑' γ, ‖actualTwoRootMarkedR U wp cp wq cq s t newR γ‖) ≤
        ((Real.exp (radius * Bp) - 1) *
          (Real.exp (radius * Bq) - 1)) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
        newRActivityFactor g CRnew p0 * Real.exp (-mu * dRoot) := by
  obtain ⟨hWeightedOld, hWeightedNew⟩ :=
    actual_U1_old_new_root_weighted oldR newR length
      g kappa0 kappaR CR CRnew p0 hg hCR hCRnew
      mu cGeo cRt dRoot hmu hgeom hOld hNew
  have hOldPos : 0 ≤ oldRActivityFactor g kappa0 CR :=
    mul_nonneg hCR (Real.rpow_pos_of_pos hg _).le
  have hNewPos : 0 ≤ newRActivityFactor g CRnew p0 :=
    mul_nonneg hCRnew (Real.exp_pos _).le
  exact ⟨
    actual_two_root_full_radius_rooted_tree
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
      oldR
      (fun γ => oldRActivityFactor g kappa0 CR *
        Real.exp (-(kappaR-mu*cGeo)*length γ))
      mu cRt dRoot (oldRActivityFactor g kappa0 CR) Nroot
      (fun γ => mul_nonneg hOldPos (Real.exp_pos _).le)
      hWeightedOld hTreeOld hU2Old,
    actual_two_root_full_radius_rooted_tree
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
      newR
      (fun γ => newRActivityFactor g CRnew p0 *
        Real.exp (-(kappaR-mu*cGeo)*length γ))
      mu cRt dRoot (newRActivityFactor g CRnew p0) Nroot
      (fun γ => mul_nonneg hNewPos (Real.exp_pos _).le)
      hWeightedNew hTreeNew hU2New⟩

end YMUIC.Original24
