import YM.OSGrowth.RootCoverCount
import YM.OSTensor.Original30RootedMaxShell

set_option autoImplicit false
noncomputable section

open Metric Set

namespace YMUIC.OSTensor
open YMUIC.OSGrowth

/-!
# Original30: derive connected polymer level counts from a rooted cover

The finite rooted-cover counting is proved by a Finset union bound and
does not enter the theorem as an unverified global cluster cardinality.
The remaining genuine physical input is the 4D cardinality bound
|K_N| <= H*2^(4N) for the actual supports and the per-root polymer
count/analytic activity bounds.
-/

theorem finite_polymer_root_cover_max_shell_growth
    {E P V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [DecidableEq P] [DecidableEq V]
    {r : ℕ} (hr : 0 < r) (n : Fin r → ℕ)
    (s : Finset P) (a : P → E → ℂ) (τ : P → ℕ)
    (K : Finset V) (rooted : V → ℕ → Finset P)
    {ρ κ σ ε B H : ℝ}
    (hρ : 0 < ρ) (hκ : σ < κ)
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hanalytic : ∀ X ∈ s, AnalyticOnNhd ℂ (a X) (ball 0 ρ))
    (hcover : ∀ X ∈ s, ∃ x ∈ K, X ∈ rooted x (τ X))
    (hrootcount : ∀ x ∈ K, ∀ k,
      ((rooted x k).card : ℝ) ≤ B * Real.exp (σ * k))
    (hKcard : (K.card : ℝ) ≤ H * (2 : ℝ) ^ (4 * Finset.univ.sup n))
    (hweight : ∀ X ∈ s, ∀ J ∈ ball 0 ρ,
      ‖a X J‖ ≤ ε * Real.exp (-κ * τ X))
    (h : Fin r → E) :
    ‖iteratedFDeriv ℂ r (normalizedPartition (polymerLog s a)) 0 h‖ ≤
      (Real.exp 1 *
        (2 * Real.exp 1 *
          (1 + ε * (H * B) / (1 - Real.exp (-(κ - σ)))) / ρ) ^ r *
          r.factorial) *
        (2 : ℝ) ^ (4 * r * Finset.univ.sup n) *
          ∏ j, ‖h j‖ := by
  let t : ℝ := (2 : ℝ) ^ (4 * Finset.univ.sup n)
  have hC : 0 ≤ H * B := mul_nonneg hH hB
  have hcount : ∀ k,
      ((s.filter (fun X => τ X = k)).card : ℝ) ≤
        ((H * B) * t) * Real.exp (σ * k) := by
    intro k
    have hc := polymer_level_count_of_root_cover s K τ rooted
      hcover hrootcount k
    have hKB : (K.card : ℝ) * B ≤ (H * t) * B :=
      mul_le_mul_of_nonneg_right hKcard hB
    have hk :
        ((K.card : ℝ) * B) * Real.exp (σ * k) ≤
          ((H * B) * t) * Real.exp (σ * k) := by
      calc
        _ ≤ ((H * t) * B) * Real.exp (σ * k) :=
          mul_le_mul_of_nonneg_right hKB (Real.exp_pos _).le
        _ = ((H * B) * t) * Real.exp (σ * k) := by ring
    exact hc.trans hk
  exact finite_polymer_max_shell_schwinger_growth
    hr n s a τ hρ hκ hε hC hanalytic hcount hweight h

end YMUIC.OSTensor
