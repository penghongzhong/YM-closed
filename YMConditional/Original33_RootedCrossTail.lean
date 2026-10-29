import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false
noncomputable section
namespace YMUIC.ConditionalCluster

open Filter
open scoped Topology BigOperators

variable {Cluster : Type*}

/-- One physical-rooted connected-polymer level, not a formal proxy for the
full Wilson path measure. -/
def crossLevel (F : ℕ → Finset Cluster) (a : Cluster → ℂ) (n : ℕ) : ℂ :=
  ∑ γ ∈ F n, a γ

/-- The exact per-polymer exponential bound and the rooted counting estimate
produce the uniform level-by-level bound; the constants are fixed before
cutoff and volume. -/
theorem rooted_count_to_level_bound
    {κ σ ε Cnt : ℝ} (hε : 0 ≤ ε)
    (F : ℕ → Finset Cluster) (a : Cluster → ℂ)
    (hcount : ∀ n, ((F n).card : ℝ) ≤ Cnt * Real.exp (σ * (n : ℝ)))
    (hweight : ∀ n γ, γ ∈ F n → ‖a γ‖ ≤ ε * Real.exp (-κ * (n : ℝ)))
    (n : ℕ) :
    ‖crossLevel F a n‖ ≤ ε * Cnt * (Real.exp (-(κ - σ))) ^ n := by
  have hper : 0 ≤ ε * Real.exp (-κ * (n : ℝ)) := by positivity
  have hseries :
      ‖crossLevel F a n‖ ≤ (F n).card * (ε * Real.exp (-κ * (n : ℝ))) := by
    calc
      ‖crossLevel F a n‖ ≤ ∑ γ ∈ F n, ‖a γ‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ γ ∈ F n, ε * Real.exp (-κ * (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact hweight n γ hγ
      _ = (F n).card * (ε * Real.exp (-κ * (n : ℝ))) := by simp
  have hc := mul_le_mul_of_nonneg_right (hcount n) hper
  calc
    ‖crossLevel F a n‖ ≤ (F n).card * (ε * Real.exp (-κ * (n : ℝ))) := hseries
    _ ≤ (Cnt * Real.exp (σ * (n : ℝ))) *
        (ε * Real.exp (-κ * (n : ℝ))) := by
          exact_mod_cast hc
    _ = ε * Cnt * (Real.exp (-(κ-σ))) ^ n := by
      rw [← Real.exp_nat_mul]
      calc
        (Cnt * Real.exp (σ * (n : ℝ))) * (ε * Real.exp (-κ * (n : ℝ))) =
            ε * Cnt * (Real.exp (σ * (n : ℝ)) * Real.exp (-κ * (n : ℝ))) := by ring
        _ = ε * Cnt * Real.exp (σ * (n : ℝ) + -κ * (n : ℝ)) := by rw [Real.exp_add]
        _ = ε * Cnt * Real.exp ((n : ℝ) * -(κ - σ)) := by congr 1; ring

#print axioms rooted_count_to_level_bound
end YMUIC.ConditionalCluster
