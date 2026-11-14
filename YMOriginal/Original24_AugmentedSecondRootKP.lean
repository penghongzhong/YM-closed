import YMOriginal.Original24_PeriodicRootTreeLimit

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Correct U2 route when the second external root can be a hub

The second Wilson root q need NOT be a leaf in an extended hard-core
connected tree. We therefore adjoin it as a SINGLE NEW POLYMER SPECIES
with support rootQ, size |rootQ| and positive fugacity epsilon.
The original physical bulk species and U1 activities remain unchanged.

Here we prove that the original unmarked per-block U1 bound plus
ONE explicit margin controls the augmented species U1 norm and
therefore the SAME previously kernel-verified U2 KP finite-height
recursion, including branching at q. No already-bounded two-root
cluster series or arbitrary FP summation is a premise.

Identifying the one-q coefficient of this augmented rooted-tree
recursion with the exact extended Penrose n+2 graph trees remains
a distinct combinatorial task.
-/

/-- Real bulk species plus ONE named second Wilson root species. -/
def actualSecondRootAugmentedSupport
    {Γ : Type*} (N : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (rootQ : Finset (PeriodicBlock N)) :
    Sum Γ Unit → Finset (PeriodicBlock N)
  | Sum.inl X => support X
  | Sum.inr _ => rootQ

/-- Keep the original physical complex activities and give the
single second-root species an explicit real positive fugacity. -/
def actualSecondRootAugmentedActivity
    {Γ : Type*} (z : Γ → ℂ) (epsilon : ℝ) : Sum Γ Unit → ℂ
  | Sum.inl X => z X
  | Sum.inr _ => (epsilon : ℂ)

/-- A second Wilson root is charged its ACTUAL finite support size;
bulk length/distance data stay unchanged. -/
def actualSecondRootAugmentedSize
    {Γ : Type*} (d : Γ → ℕ) (rootCard : ℕ) : Sum Γ Unit → ℕ
  | Sum.inl X => d X
  | Sum.inr _ => rootCard

/-- The per-block U1 activity of the augmented physical model
splits EXACTLY into the unchanged bulk U1 norm and at most
epsilon * exp(kappa * |rootQ|) from one second-root species. -/
theorem actual_second_root_augmented_local_U1
    {Γ : Type*} [Fintype Γ]
    (N : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (rootQ : Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa aAct epsilon : ℝ)
    (heps : 0 ≤ epsilon)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct) :
    ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock
        (actualSecondRootAugmentedSupport N support rootQ) Delta,
        ‖actualSecondRootAugmentedActivity z epsilon Y‖ *
          Real.exp (kappa *
            (actualSecondRootAugmentedSize d rootQ.card Y : ℝ))) ≤
      aAct + epsilon * Real.exp (kappa * (rootQ.card : ℝ)) := by
  classical
  intro Delta
  have hSplit :
      (∑ Y ∈ actualThroughBlock
        (actualSecondRootAugmentedSupport N support rootQ) Delta,
        ‖actualSecondRootAugmentedActivity z epsilon Y‖ *
          Real.exp (kappa *
            (actualSecondRootAugmentedSize d rootQ.card Y : ℝ))) =
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) +
        (if Delta ∈ rootQ then
           epsilon * Real.exp (kappa * (rootQ.card : ℝ)) else 0) := by
    simp only [actualThroughBlock, Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    simp [actualSecondRootAugmentedSupport,
      actualSecondRootAugmentedActivity, actualSecondRootAugmentedSize,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg heps]
    rfl
  rw [hSplit]
  have hepsNonneg :
      0 ≤ epsilon * Real.exp (kappa * (rootQ.card : ℝ)) :=
    mul_nonneg heps (Real.exp_pos _).le
  have hboundIf :
      (if Delta ∈ rootQ then
        epsilon * Real.exp (kappa * (rootQ.card : ℝ)) else 0) ≤
      epsilon * Real.exp (kappa * (rootQ.card : ℝ)) := by
    split_ifs <;> simp [hepsNonneg]
  linarith [hLocalNorm Delta]

/-- Explicit finite-activity KP budget for the augmented model,
where the second Wilson root can branch: children are the SAME
actual physical 4D periodic contact neighbors. -/
theorem actual_second_root_augmented_U2_KP
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct epsilon : ℝ)
    (haAct : 0 ≤ aAct) (heps : 0 ≤ epsilon)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (aAct + epsilon * Real.exp
          (kappa * (rootQ.card : ℝ))) ≤
        (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct) :
    ∀ h,
      actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity z epsilon)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu h ≤
      ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (rootP.card : ℝ)) *
        (aAct + epsilon * Real.exp
          (kappa * (rootQ.card : ℝ))) := by
  have hSizeAug : ∀ Y : Sum Γ Unit,
      (actualSecondRootAugmentedSupport N support rootQ Y).card ≤
      actualSecondRootAugmentedSize d rootQ.card Y := by
    intro Y
    cases Y with
    | inl X =>
        change (support X).card ≤ d X
        exact hsize X
    | inr _ =>
        change rootQ.card ≤ rootQ.card
        exact le_refl _
  have hLocalAug :=
    actual_second_root_augmented_local_U1 N support rootQ z d
      kappa aAct epsilon heps hLocalNorm
  exact actual_periodic_first_root_uniform N chi rootP
    (actualSecondRootAugmentedSupport N support rootQ)
    (actualSecondRootAugmentedActivity z epsilon)
    (actualSecondRootAugmentedSize d rootQ.card)
    kappa mu cGeo
    (aAct + epsilon * Real.exp (kappa * (rootQ.card : ℝ)))
    (add_nonneg haAct
      (mul_nonneg heps (Real.exp_pos _).le))
    hdelta hSizeAug hsmall hLocalAug

end YMUIC.Original24
