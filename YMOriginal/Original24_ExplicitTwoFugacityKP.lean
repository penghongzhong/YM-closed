import YMOriginal.Original24_DoubleFugacitySelection
import YMOriginal.Original24_AugmentedSecondRootKP
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Concrete double-fugacity U1/KP bound with recovered O(aAct) factor

Under 4 B aAct <= delta, and aAct>0, choose
  lambda  = delta/(4 B aAct),   epsilon = delta/(8 B E),
  B=(2chi+1)^4, E=exp(kappa |rootQ|),
  delta=kappa-cGeo*mu.
Then lambda>=1, epsilon>0 and
  B (lambda aAct + epsilon E) = 3 delta/8 < delta/2.

The ORIGINAL physical bulk activity z is simply rescaled by lambda,
and q is adjoined as exactly one distinguished species of activity eps.
The previously strict-verified U1 -> augmented KP now gives a
FULL positive p-root forest bound with no new smallness hypothesis.

Moreover 1/(lambda epsilon) is proportional to aAct, so extracting
trees with exactly one q and at least one bulk via the preceding
positive combinatorial lemma restores the required O(aAct) factor.
The labeled-tree-to-KP FP identification is still a distinct theorem
from the published combinatorial source, not assumed proved here.
-/

/-- Explicit positive two-fugacity choice from a precise U1/KP
weak-coupling margin. Every numerical coefficient is checked. -/
theorem original24_explicit_double_fugacity_margin
    (B E aAct delta : ℝ)
    (hB : 0 < B) (hE : 0 < E) (hAct : 0 < aAct)
    (hdelta : 0 < delta)
    (hsmall : 4 * B * aAct ≤ delta) :
    ∃ lam eps : ℝ,
      1 ≤ lam ∧ 0 < eps ∧
      B * (lam * aAct + eps * E) ≤ delta / 2 ∧
      (lam * eps) * (32 * B ^ 2 * E * aAct / delta ^ 2) = 1 := by
  let lam : ℝ := delta / (4 * B * aAct)
  let eps : ℝ := delta / (8 * B * E)
  have hdenLam : 0 < 4 * B * aAct := by positivity
  have hdenEps : 0 < 8 * B * E := by positivity
  have hlam : 1 ≤ lam := by
    change 1 ≤ delta / (4 * B * aAct)
    apply (le_div_iff₀ hdenLam).mpr
    nlinarith [hsmall]
  have heps : 0 < eps := div_pos hdelta hdenEps
  have hfirst : B * (lam * aAct) = delta / 4 := by
    dsimp [lam]
    field_simp [ne_of_gt hB, ne_of_gt hAct] <;> ring
  have hsecond : B * (eps * E) = delta / 8 := by
    dsimp [eps]
    field_simp [ne_of_gt hB, ne_of_gt hE] <;> ring
  have hKP : B * (lam * aAct + eps * E) ≤ delta / 2 := by
    have hEq :
        B * (lam * aAct + eps * E) =
          B * (lam * aAct) + B * (eps * E) := by ring
    rw [hEq, hfirst, hsecond]
    linarith [hdelta]
  have hproduct :
      (lam * eps) * (32 * B ^ 2 * E * aAct / delta ^ 2) = 1 := by
    dsimp [lam, eps]
    field_simp [ne_of_gt hB, ne_of_gt hE,
      ne_of_gt hAct, ne_of_gt hdelta]
    ring
  exact ⟨lam, eps, hlam, heps, hKP, hproduct⟩

/-- From the original U1 local norm alone, plus a precise strict
smallness margin, construct double positive fugacities and prove
uniform FULL p-rooted nonempty forest bound for the q-augmented
four-dimensional periodic polymer system at ALL finite heights.

There is no hAug, no assumed second-root tree-sum bound, and no
already-bounded connected Ursell series in the hypotheses. -/
theorem original24_actual_double_fugacity_root_forest_from_U1
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (haAct : 0 < aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
        kappa - cGeo * mu)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct) :
    ∃ lam eps : ℝ, 1 ≤ lam ∧ 0 < eps ∧
      (lam * eps) *
        (32 *
          ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) ^ 2) *
          Real.exp (kappa * (rootQ.card : ℝ)) *
          aAct / (kappa - cGeo * mu) ^ 2) = 1 ∧
      ∀ h : ℕ,
        Real.exp
          (actualPeriodicFirstRootSum N chi rootP
            (actualSecondRootAugmentedSupport N support rootQ)
            (actualSecondRootAugmentedActivity
              (fun X => (lam : ℂ) * z X) eps)
            (actualSecondRootAugmentedSize d rootQ.card)
            cGeo mu h) - 1 ≤
          Real.exp ((rootP.card : ℝ) *
            ((kappa - cGeo * mu) / 2)) - 1 := by
  let B : ℝ := (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ)
  let E : ℝ := Real.exp (kappa * (rootQ.card : ℝ))
  let delta : ℝ := kappa - cGeo * mu
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨lam, eps, hlam, heps, hmargin, hproduct⟩ :=
    original24_explicit_double_fugacity_margin B E aAct delta
      hB hE haAct hdelta hsmall
  let zScaled : Γ → ℂ := fun X => (lam : ℂ) * z X
  have hlam0 : 0 ≤ lam := by linarith
  have hlocalScaled : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖zScaled X‖ * Real.exp (kappa * (d X : ℝ))) ≤
          lam * aAct := by
    intro Delta
    have hterm (X : Γ) :
        ‖zScaled X‖ * Real.exp (kappa * (d X : ℝ)) =
          lam * (‖z X‖ * Real.exp (kappa * (d X : ℝ))) := by
      dsimp [zScaled]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlam0]
      ring
    calc
      (∑ X ∈ actualThroughBlock support Delta,
        ‖zScaled X‖ * Real.exp (kappa * (d X : ℝ))) =
        ∑ X ∈ actualThroughBlock support Delta,
          lam * (‖z X‖ * Real.exp (kappa * (d X : ℝ))) := by
            apply Finset.sum_congr rfl
            intro X _
            exact hterm X
      _ = lam * (∑ X ∈ actualThroughBlock support Delta,
          ‖z X‖ * Real.exp (kappa * (d X : ℝ))) := by
            rw [Finset.mul_sum]
      _ ≤ lam * aAct :=
        mul_le_mul_of_nonneg_left (hLocalNorm Delta) hlam0
  have hKP : ∀ h,
      actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity zScaled eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu h ≤
      ((B * (rootP.card : ℝ)) *
        (lam * aAct + eps * E)) := by
    exact actual_second_root_augmented_U2_KP
      N chi rootP rootQ support zScaled d
      kappa mu cGeo (lam * aAct) eps
      (mul_nonneg hlam0 haAct.le) heps.le hdelta hsize
      hmargin hlocalScaled
  have hcard : 0 ≤ (rootP.card : ℝ) := Nat.cast_nonneg _
  have hUniform :
      (B * (rootP.card : ℝ)) *
        (lam * aAct + eps * E) ≤
      (rootP.card : ℝ) * (delta / 2) := by
    calc
      _ = (rootP.card : ℝ) *
        (B * (lam * aAct + eps * E)) := by ring
      _ ≤ (rootP.card : ℝ) * (delta / 2) :=
        mul_le_mul_of_nonneg_left hmargin hcard
  refine ⟨lam, eps, hlam, heps, ?_, ?_⟩
  · simpa only [B, E, delta] using hproduct
  · intro h
    change Real.exp
      (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity zScaled eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu h) - 1 ≤
          Real.exp ((rootP.card : ℝ) * (delta / 2)) - 1
    exact sub_le_sub_right
      (Real.exp_le_exp.mpr ((hKP h).trans hUniform)) 1

end YMUIC.Original24
