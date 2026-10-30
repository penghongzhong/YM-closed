import YMOriginal.Original24_AugmentedSecondRootKP
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Actual strictly positive fugacity for the second Wilson root

The augmented KP construction must not require a freely assumed
sufficiently small second-root fugacity. A strict U1 weak-coupling
margin yields a SPECIFIC positive epsilon, independent of the
regulator/cutoff and volume when the original uniform parameters
and fixed root complexity are uniform.

The resulting augmented q-root species is allowed to branch,
unlike an invalid reduction that deletes q from every extended
two-root Penrose tree. The remaining external combinatorial step
is identification of the exact ONE-q coefficient of the augmented
rooted tree sum with the original extended n+2 Mayer trees.
-/

/-- Elementary constructive root fugacity from a STRICT available
KP margin: epsilon = (H-B*A)/(2*B*E). -/
theorem positive_second_root_fugacity_of_margin
    (B E A H : ℝ)
    (hB : 0 < B) (hE : 0 < E)
    (hMargin : B * A < H) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      B * (A + epsilon * E) ≤ H := by
  let epsilon : ℝ := (H - B * A) / (2 * B * E)
  have hD : 0 < 2 * B * E := by positivity
  have hNum : 0 < H - B * A := sub_pos.mpr hMargin
  have heps : 0 < epsilon := div_pos hNum hD
  have hId : (2 * B * E) * epsilon = H - B * A := by
    dsimp [epsilon]
    field_simp [ne_of_gt hD]
  refine ⟨epsilon, heps, ?_⟩
  nlinarith [hId]

/-- From STRICT physical U1/KP smallness, we EXHIBIT a strictly
positive second-root fugacity and derive the UNIFORM augmented
first-root tree bound for all finite heights.

There is no independent hsmall_aug, no one-q tree bound, and no
assumed complete two-root Ursell cumulant estimate. -/
theorem actual_positive_second_root_KP_from_U1_margin
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (haAct : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hmargin :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct <
        (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
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
  let B : ℝ := ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ)
  let E : ℝ := Real.exp (kappa * (rootQ.card : ℝ))
  let H : ℝ := (kappa - cGeo * mu) / 2
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨eps, heps, hSmallRaw⟩ :=
    positive_second_root_fugacity_of_margin
      B E aAct H hB hE hmargin
  have hSmall :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (aAct + eps * Real.exp (kappa * (rootQ.card : ℝ))) ≤
          (kappa - cGeo * mu) / 2 := by
    simpa only [B, E, H] using hSmallRaw
  refine ⟨eps, heps, ?_⟩
  exact actual_second_root_augmented_U2_KP
    N chi rootP rootQ support z d
    kappa mu cGeo aAct eps
    haAct heps.le hdelta hsize hSmall hLocalNorm

end YMUIC.Original24
