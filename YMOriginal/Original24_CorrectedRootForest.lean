import YMOriginal.Original24_PeriodicRootTreeLimit
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Correct external-root UNORDERED FOREST factor (not one child)

The old C29 U2 proof treated
  S_h(p) = sum_{X touches p} w(X) F_h(X)
as the complete p-rooted tree count, but the source root can have
an ARBITRARY number of bulk children. The exponential formula gives
  exp(S_h(p)) - 1
for nonempty unordered child forests, not merely S_h(p).

We strictly prove that the genuine positive first-root sum produced
by U1/KP still yields a UNIFORM, cutoff-independent root forest
bound of order aAct:
  exp(S_h)-1 <= M * exp(M),
  M=(2chi+1)^4 |root| aAct.
The missing second-marked-root (r_q) combinatorics is NOT claimed
resolved by this one-root correction.
-/

/-- The exact elementary nonnegative exponential forest gain.
For x >= 0, exp(x)-1 <= x exp(x). -/
theorem original24_exp_forest_le
    (x : ℝ) (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hneg : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have hexp : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    have hz : -x + x = 0 := by ring
    rw [hz, Real.exp_zero]
  have hmul :=
    mul_le_mul_of_nonneg_right hneg (Real.exp_pos x).le
  nlinarith

/-- The actual complete p-rooted nonempty child FOREST factor of
the already verified U2 periodic finite-height recursion. -/
def actualPeriodicNonemptyRootForest
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu : ℝ) (h : ℕ) : ℝ :=
  Real.exp
    (actualPeriodicFirstRootSum N chi root support z d cGeo mu h) - 1

/-- Replace the incorrect single-child root combinatorics by the
correct exponential-FORMULA complete forest. It still costs at most
M*exp(M) uniformly in EVERY finite tree height and cutoff N.
No assumption on root-forest total is passed as a premise. -/
theorem actual_periodic_full_root_forest_from_U1
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct) :
    ∀ h,
      actualPeriodicNonemptyRootForest N chi root support
        z d cGeo mu h ≤
      (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ)) * aAct) *
      Real.exp (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ)) * aAct) := by
  let M : ℝ :=
    ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (root.card : ℝ)) * aAct
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hS := actual_periodic_first_root_uniform
    N chi root support z d kappa mu cGeo aAct ha
    hdelta hsize hsmall hLocalNorm
  intro h
  have hExp := Real.exp_le_exp.mpr (hS h)
  change Real.exp
      (actualPeriodicFirstRootSum N chi root support z d cGeo mu h) - 1 ≤
    M * Real.exp M
  calc
    Real.exp
      (actualPeriodicFirstRootSum N chi root support z d cGeo mu h) - 1 ≤
        Real.exp M - 1 := sub_le_sub_right hExp 1
    _ ≤ M * Real.exp M := original24_exp_forest_le M hM

end YMUIC.Original24
