import YM.Wilson.OrderedDualSourceRG21
import YM.Wilson.CandidateGramPolynomial21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Explicit composite 21-template Wilson source through the true RG order

Each of the 21 source channels is an ACTUAL finite polynomial built from
six SU(2) plaquette holonomies at a common basepoint; the polynomial has
an exact coefficient budget.  The old C29 source pairing is then
applied through the true left-ordered RG matrices. No cumulative RG
norm is assumed. The actual physical a-dependent normalization,
classical jet matching and one-step matrix identity remain MODEL inputs.
-/

/-- One composite polynomial source per 21-dimensional RG source channel. -/
def fixedCompositeGramSource
    {T : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (templates : RootFiber21 → T → List RootFiber21)
    (coeff : RootFiber21 → T → ℂ)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) : RootFiber21 → ℂ :=
  fun α => candidateGramPolynomialSchwartzSource
    U (templates α) (coeff α) (position α) f

/-- Exact all-scale bilinear source estimate with no cumulative source
norm. Every normalization loss is visible in the coefficient budget. -/
theorem fixed_composite_gram_paired_rg_bound
    {T : Type*} [Fintype T]
    (C B : ℕ → SourceRGMatrix21)
    (hstep : ∀ (n : ℕ) (k j : RootFiber21),
      (∑ i : RootFiber21, C n i k * B n i j) =
        if k = j then 1 else 0)
    (J : RootFiber21 → ℂ)
    (U : GramPlaquette6 → SU2)
    (templates : RootFiber21 → T → List RootFiber21)
    (coeff : RootFiber21 → T → ℂ)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n : ℕ,
      ‖∑ i : RootFiber21,
        sourceRGAction (leftOrderedSourceRGChain C n)
          (fixedCompositeGramSource U templates coeff position f) i *
        sourceRGAction (leftOrderedSourceRGChain B n) J i‖ ≤
      (∑ α : RootFiber21,
         ‖J α‖ * candidateGramPolynomialBudget (templates α) (coeff α)) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  rw [source_paired_left_ordered_rg_chain C B hstep
      (fixedCompositeGramSource U templates coeff position f) J n]
  have hsrc (α : RootFiber21) :
      ‖fixedCompositeGramSource U templates coeff position f α‖ ≤
        candidateGramPolynomialBudget (templates α) (coeff α) *
          SchwartzMap.seminorm ℂ 0 0 f :=
    candidate_gram_polynomial_schwartz_bound
      U (templates α) (coeff α) (position α) f
  calc
    ‖∑ α : RootFiber21,
      fixedCompositeGramSource U templates coeff position f α * J α‖ ≤
      ∑ α : RootFiber21,
        ‖fixedCompositeGramSource U templates coeff position f α * J α‖ :=
          norm_sum_le _ _
    _ = ∑ α : RootFiber21,
        ‖fixedCompositeGramSource U templates coeff position f α‖ *
          ‖J α‖ := by simp only [norm_mul]
    _ ≤ ∑ α : RootFiber21,
        (candidateGramPolynomialBudget (templates α) (coeff α) *
          SchwartzMap.seminorm ℂ 0 0 f) * ‖J α‖ := by
            apply Finset.sum_le_sum
            intro α hα
            exact mul_le_mul_of_nonneg_right (hsrc α) (norm_nonneg _)
    _ = (∑ α : RootFiber21,
         ‖J α‖ * candidateGramPolynomialBudget (templates α) (coeff α)) *
          SchwartzMap.seminorm ℂ 0 0 f := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro α hα
            ring

/-- A genuine shared coefficient budget K suffices for the all-scale
PAIRED composite-source estimate, still without a bound on Z_n. The
budget and inverse-transpose inputs are explicit model obligations. -/
theorem fixed_composite_gram_paired_rg_uniform
    {T : Type*} [Fintype T]
    (C B : ℕ → SourceRGMatrix21)
    (hstep : ∀ (n : ℕ) (k j : RootFiber21),
      (∑ i : RootFiber21, C n i k * B n i j) =
        if k = j then 1 else 0)
    (J : RootFiber21 → ℂ)
    (U : GramPlaquette6 → SU2)
    (templates : RootFiber21 → T → List RootFiber21)
    (coeff : RootFiber21 → T → ℂ)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ)
    (K : ℝ) (_hK : 0 ≤ K)
    (hbudget : ∀ α, candidateGramPolynomialBudget
      (templates α) (coeff α) ≤ K) :
    ∀ n : ℕ,
      ‖∑ i : RootFiber21,
        sourceRGAction (leftOrderedSourceRGChain C n)
          (fixedCompositeGramSource U templates coeff position f) i *
        sourceRGAction (leftOrderedSourceRGChain B n) J i‖ ≤
        K * (∑ α : RootFiber21, ‖J α‖) *
          SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  have hsum :
      (∑ α : RootFiber21,
         ‖J α‖ * candidateGramPolynomialBudget (templates α) (coeff α)) ≤
        K * (∑ α : RootFiber21, ‖J α‖) := by
    calc
      _ ≤ ∑ α : RootFiber21, ‖J α‖ * K := by
            apply Finset.sum_le_sum
            intro α hα
            exact mul_le_mul_of_nonneg_left (hbudget α) (norm_nonneg _)
      _ = K * ∑ α : RootFiber21, ‖J α‖ := by
            rw [← Finset.sum_mul]
            ring
  calc
    _ ≤ (∑ α : RootFiber21,
        ‖J α‖ * candidateGramPolynomialBudget (templates α) (coeff α)) *
          SchwartzMap.seminorm ℂ 0 0 f :=
        fixed_composite_gram_paired_rg_bound
          C B hstep J U templates coeff position f n
    _ ≤ K * (∑ α : RootFiber21, ‖J α‖) *
          SchwartzMap.seminorm ℂ 0 0 f :=
        mul_le_mul_of_nonneg_right hsum (apply_nonneg _ _)

end YMUIC.Wilson
