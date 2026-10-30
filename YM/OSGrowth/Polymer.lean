import YM.OSGrowth.Moments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

open Metric Set Filter
open scoped Topology BigOperators

namespace YMUIC.OSGrowth

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def polymerLog (s : Finset P) (a : P → E → ℂ) (J : E) : ℂ :=
  ∑ X ∈ s, a X J

theorem polymerLog_analytic {s : Finset P} {a : P → E → ℂ} {ρ : ℝ}
    (ha : ∀ X ∈ s, AnalyticOnNhd ℂ (a X) (ball 0 ρ)) :
    AnalyticOnNhd ℂ (polymerLog s a) (ball 0 ρ) :=
  s.analyticOnNhd_fun_sum ha

omit [NormedSpace ℂ E] in
theorem polymerLog_bound {s : Finset P} (a : P → E → ℂ) (τ : P → ℕ)
    {κ σ ε C ρ : ℝ} (hκ : σ < κ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hcount : ∀ n, ((s.filter (fun X => τ X = n)).card : ℝ) ≤ C * Real.exp (σ * n))
    (hweight : ∀ X ∈ s, ∀ J ∈ ball 0 ρ, ‖a X J‖ ≤ ε * Real.exp (-κ * τ X)) :
    ∀ J ∈ ball 0 ρ, ‖polymerLog s a J‖ ≤ ε * C / (1 - Real.exp (-(κ - σ))) := by
  classical
  intro J hJ
  let q : ℝ := Real.exp (-(κ - σ))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; linarith
  have hmajor : Summable (fun n : ℕ => ε * C * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (ε * C)
  have hlevel (n : ℕ) : ∑ X ∈ s with τ X = n, ‖a X J‖ ≤ ε * C * q ^ n := by
    calc
      _ ≤ ∑ X ∈ s with τ X = n, ε * Real.exp (-κ * n) := by
        apply Finset.sum_le_sum
        intro X hX
        obtain ⟨hXs, hXn⟩ := Finset.mem_filter.mp hX
        simpa only [hXn] using hweight X hXs J hJ
      _ = ((s.filter (fun X => τ X = n)).card : ℝ) * (ε * Real.exp (-κ * n)) := by simp
      _ ≤ (C * Real.exp (σ * n)) * (ε * Real.exp (-κ * n)) :=
        mul_le_mul_of_nonneg_right (hcount n) (by positivity)
      _ = ε * C * q ^ n := by
        dsimp [q]
        rw [← Real.exp_nat_mul]
        calc
          _ = ε * C * (Real.exp (σ * n) * Real.exp (-κ * n)) := by ring
          _ = ε * C * Real.exp (σ * n + -κ * n) := by rw [Real.exp_add]
          _ = _ := by congr 2; ring
  calc
    ‖polymerLog s a J‖ ≤ ∑ X ∈ s, ‖a X J‖ := norm_sum_le _ _
    _ = ∑ n ∈ s.image τ, ∑ X ∈ s with τ X = n, ‖a X J‖ :=
      (Finset.sum_fiberwise_of_maps_to (fun X hX => Finset.mem_image_of_mem τ hX) _).symm
    _ ≤ ∑ n ∈ s.image τ, ε * C * q ^ n := Finset.sum_le_sum (fun n _ => hlevel n)
    _ ≤ ∑' n : ℕ, ε * C * q ^ n :=
      hmajor.sum_le_tsum (s.image τ) (fun n _ => by positivity)
    _ = ε * C / (1 - q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

end YMUIC.OSGrowth
