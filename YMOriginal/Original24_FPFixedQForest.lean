import YMOriginal.Original24_FPFixedQFactorial
import YMOriginal.Original24_ExplicitTwoFugacityKP

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Full-height positive KP forest with a FIXED second-root q slot

To avoid the unnecessary exact orbit enumeration of q over n+1
positions, reserve q in one non-root position, use
  (n+1)/2^n <= 1,
and double the bulk fugacity in the standard published FP comparison.

The only analytic price is the stronger physical U1 margin
  8 (2chi+1)^4 aAct <= kappa-cGeo*mu
instead of 4 times. Reuse the ALREADY KERNEL-CHECKED actual periodic
double-fugacity KP recursion on bulk data (2*z,2*aAct); there is
no new abstract rooted-tree or final hFP hypothesis.

The exact positive finite-height forest output holds at EVERY h
for actual four-dimensional periodic supports and branching q.
-/

/-- Strict doubled-source KP bound: all finite heights are controlled
with explicitly constructed lambda, epsilon and 1/(lambda*epsilon)
proportional to the physical unmarked U1 activity aAct.

The full Mayer/FP labeled-tree enumeration is a separate remaining
published-combinatorics interface; nothing about that sum is
assumed or asserted as a consequence of this theorem alone. -/
theorem original24_fixed_q_doubled_bulk_KP_from_U1
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (haAct : 0 < aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall8 :
      8 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
        kappa - cGeo * mu)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct) :
    ∃ lam eps : ℝ,
      1 ≤ lam ∧ 0 < eps ∧
      (lam * eps) *
        (64 * (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) ^ 2) *
          Real.exp (kappa * (rootQ.card : ℝ)) *
          aAct / (kappa - cGeo * mu) ^ 2) = 1 ∧
      ∀ h : ℕ,
        Real.exp
          (actualPeriodicFirstRootSum N chi rootP
            (actualSecondRootAugmentedSupport N support rootQ)
            (actualSecondRootAugmentedActivity
              (fun X => (lam : ℂ) * ((2 : ℂ) * z X)) eps)
            (actualSecondRootAugmentedSize d rootQ.card)
            cGeo mu h) - 1 ≤
        Real.exp ((rootP.card : ℝ) *
            ((kappa - cGeo * mu) / 2)) - 1 := by
  have h2norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have h2Local : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖(2 : ℂ) * z X‖ * Real.exp (kappa * (d X : ℝ))) ≤
          2 * aAct := by
    intro Delta
    calc
      _ = 2 * (∑ X ∈ actualThroughBlock support Delta,
          ‖z X‖ * Real.exp (kappa * (d X : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro X hX
        rw [norm_mul, h2norm]
        ring
      _ ≤ 2 * aAct :=
        mul_le_mul_of_nonneg_left (hLocalNorm Delta) (by norm_num)
  have h2Small :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * (2 * aAct) ≤
        kappa - cGeo * mu := by
    nlinarith [hsmall8]
  obtain ⟨lam, eps, hlam, heps, hprod, hforest⟩ :=
    original24_actual_double_fugacity_root_forest_from_U1
      N chi rootP rootQ support (fun X => (2 : ℂ) * z X) d
      kappa mu cGeo (2 * aAct)
      (by positivity) hdelta hsize h2Small h2Local
  refine ⟨lam, eps, hlam, heps, ?_, hforest⟩
  convert hprod using 1 <;> ring

end YMUIC.Original24
