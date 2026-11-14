import YMOriginal.Original24_ActualWordMarked

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# U1 unmarked R -> U2 root-weighted tree bound: actual geometry interface

Derive the exact weighted input of the Original24 marked source
from only (i) an unmarked U1 activity bound, (ii) the genuine
root/support distance bound and (iii) the one-time choice of mu.
The remaining summability of the transformed tree weights is
the separately verified U2 rooted-tree counting/majorant obligation.

This does not change the physical native distance or assume that
the CMP122 relative length is equal to the new manuscript's length.
-/

/-- The exponential root-distance weighted bound is derived from a
native geometric distance dictionary and an unmarked R-sector bound. -/
theorem weighted_root_from_unmarked_distance
    {Γ : Type*}
    (z : Γ → ℂ) (length : Γ → ℝ)
    (kappa mu cGeo cRt dRoot A : ℝ)
    (hmu : 0 ≤ mu) (_hA : 0 ≤ A)
    (hgeom : ∀ γ, dRoot ≤ cRt + cGeo * length γ)
    (hunmarked : ∀ γ,
      ‖z γ‖ ≤ A * Real.exp (-kappa * length γ)) :
    ∀ γ,
      Real.exp (mu * dRoot) * ‖z γ‖ ≤
        Real.exp (mu * cRt) *
          (A * Real.exp (-(kappa - mu * cGeo) * length γ)) := by
  intro γ
  have hscale : mu * dRoot ≤
      mu * (cRt + cGeo * length γ) :=
    mul_le_mul_of_nonneg_left (hgeom γ) hmu
  have hExp : Real.exp (mu * dRoot) ≤
      Real.exp (mu * (cRt + cGeo * length γ)) :=
    Real.exp_le_exp.mpr hscale
  calc
    Real.exp (mu * dRoot) * ‖z γ‖ ≤
        Real.exp (mu * (cRt + cGeo * length γ)) * ‖z γ‖ :=
      mul_le_mul_of_nonneg_right hExp (norm_nonneg _)
    _ ≤ Real.exp (mu * (cRt + cGeo * length γ)) *
        (A * Real.exp (-kappa * length γ)) :=
      mul_le_mul_of_nonneg_left (hunmarked γ) (Real.exp_pos _).le
    _ = A *
        (Real.exp (mu * (cRt + cGeo * length γ)) *
          Real.exp (-kappa * length γ)) := by ring
    _ = A * Real.exp
        (mu * (cRt + cGeo * length γ) + (-kappa * length γ)) := by
      rw [Real.exp_add]
    _ = A * Real.exp
        (mu * cRt + (-(kappa - mu * cGeo) * length γ)) := by
      congr 1
      ring
    _ = Real.exp (mu * cRt) *
        (A * Real.exp (-(kappa - mu * cGeo) * length γ)) := by
      rw [Real.exp_add]
      ring

/-- The genuinely ordered SU2 external word source is now propagated
from original unmarked R data and the actual support-distance geometry.
No marked-R analytic stability is an input. -/
theorem actual_word_rooted_sum_from_unmarked_geometry
    {P T Γ : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ) (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (unmarked : Γ → ℂ) (length : Γ → ℝ)
    (kappa mu cGeo cRt dRoot A aAct : ℝ) (Nroot : ℕ)
    (hmu : 0 ≤ mu) (hA : 0 ≤ A)
    (hgeom : ∀ γ, dRoot ≤ cRt + cGeo * length γ)
    (hunmarked : ∀ γ,
      ‖unmarked γ‖ ≤ A * Real.exp (-kappa * length γ))
    (htree : Summable
      (fun γ : Γ => A * Real.exp (-(kappa - mu * cGeo) * length γ)))
    (htreeTotal :
      (∑' γ : Γ, A * Real.exp (-(kappa - mu * cGeo) * length γ))
        ≤ (Nroot : ℝ) * aAct) :
    (∑' γ, ‖actualWordMarkedR U words coeff s unmarked γ‖) ≤
      (2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aAct * Real.exp (-mu * dRoot) := by
  exact actual_word_marked_r_sum U words coeff s hsmall
    unmarked (fun γ => A * Real.exp (-(kappa - mu * cGeo) * length γ))
    mu cRt dRoot aAct Nroot
    (fun γ => mul_nonneg hA (Real.exp_pos _).le)
    (weighted_root_from_unmarked_distance unmarked length
      kappa mu cGeo cRt dRoot A hmu hA hgeom hunmarked)
    htree htreeTotal

end YMUIC.Original24
