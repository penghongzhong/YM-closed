import Mathlib

set_option autoImplicit false

/-!
A two-dimensional guardrail for the local-to-global inference, NOT a
counterexample to Yang--Mills theory. Both the transfer form and its deficit
are nonnegative. Axis margins still do not imply a uniform relative deficit.
-/
namespace YMUICV128.Audit.T900

noncomputable def baseGram (x y : ℝ) : ℝ := x ^ 2 + y ^ 2
noncomputable def deficit (x y : ℝ) : ℝ := (x - y) ^ 2 / 2
noncomputable def transfer (x y : ℝ) : ℝ := (x + y) ^ 2 / 2

theorem gram_decomposition (x y : ℝ) :
    baseGram x y = deficit x y + transfer x y := by
  unfold baseGram deficit transfer
  ring

theorem deficit_nonneg (x y : ℝ) : 0 ≤ deficit x y := by
  unfold deficit
  positivity

theorem transfer_nonneg (x y : ℝ) : 0 ≤ transfer x y := by
  unfold transfer
  positivity

theorem positive_contraction_forms (x y : ℝ) :
    0 ≤ deficit x y ∧ deficit x y ≤ baseGram x y ∧
      0 ≤ transfer x y ∧ transfer x y ≤ baseGram x y := by
  have hd := deficit_nonneg x y
  have ht := transfer_nonneg x y
  have he := gram_decomposition x y
  exact ⟨hd, by linarith, ht, by linarith⟩

theorem axis_relative_margins (x y : ℝ) :
    deficit x 0 = (1 / 2 : ℝ) * baseGram x 0 ∧
      deficit 0 y = (1 / 2 : ℝ) * baseGram 0 y := by
  unfold deficit baseGram
  constructor <;> ring

theorem diagonal_null_deficit : deficit 1 1 = 0 ∧ baseGram 1 1 = 2 := by
  norm_num [deficit, baseGram]

theorem no_uniform_relative_deficit (eta : ℝ) (heta : 0 < eta) :
    ¬ (∀ x y : ℝ, eta * baseGram x y ≤ deficit x y) := by
  intro h
  have hd := h 1 1
  norm_num [baseGram, deficit] at hd
  linarith

theorem no_uniform_transfer_contraction (q : ℝ) (hq : q < 1) :
    ¬ (∀ x y : ℝ, transfer x y ≤ q * baseGram x y) := by
  intro h
  have ht := h 1 1
  norm_num [baseGram, transfer] at ht
  linarith

#print axioms gram_decomposition
#print axioms deficit_nonneg
#print axioms transfer_nonneg
#print axioms positive_contraction_forms
#print axioms axis_relative_margins
#print axioms diagonal_null_deficit
#print axioms no_uniform_relative_deficit
#print axioms no_uniform_transfer_contraction

end YMUICV128.Audit.T900
