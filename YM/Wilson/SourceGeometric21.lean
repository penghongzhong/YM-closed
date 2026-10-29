import YM.Wilson.DualSourceRGUniform21
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- A physically stronger, explicitly stated geometric bound on the
actual primal 21-root matrix defect implies a regulator-independent
dual-source estimate. Summability and an RG product bound are derived;
the geometric decay itself remains an upstream Wilson RG obligation. -/
theorem dual_source_wilson_geometric_rg
    (A B : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (D θ : ℝ) (hD0 : 0 ≤ D) (hDhalf : D ≤ 1 / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hrow : ∀ (n : ℕ) (β : RootFiber21),
      (∑ j : RootFiber21, ‖A n β j‖) ≤ D * θ ^ n)
    (hinv : ∀ n, DualSourceInverse (A n) (B n))
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n : ℕ,
      ‖mixedWilsonDirection (sourceCocycleChain B n) U position f‖ ≤
        4 * Real.exp (2 * (D / (1 - θ))) *
          SchwartzMap.seminorm ℂ 0 0 f := by
  have hδ0 (n : ℕ) : 0 ≤ D * θ ^ n :=
    mul_nonneg hD0 (pow_nonneg hθ0 _)
  have hδhalf (n : ℕ) : D * θ ^ n ≤ 1 / 2 := by
    calc
      D * θ ^ n ≤ D * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hθ0 hθ1.le) hD0
      _ = D := by ring
      _ ≤ 1 / 2 := hDhalf
  have hδsum : Summable (fun n : ℕ => D * θ ^ n) :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left D
  have hδtsum : (∑' n : ℕ, D * θ ^ n) = D / (1 - θ) := by
    simp only [tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1, div_eq_mul_inv]
  have hδbudget (n : ℕ) :
      (∑ j ∈ Finset.range n, D * θ ^ j) ≤ D / (1 - θ) := by
    calc
      _ ≤ ∑' j : ℕ, D * θ ^ j :=
        hδsum.sum_le_tsum (Finset.range n) (fun j hj => hδ0 j)
      _ = D / (1 - θ) := hδtsum
  exact dual_source_wilson_rg_uniform A B
    (fun n => D * θ ^ n) hδ0 hδhalf hrow hinv
    (D / (1 - θ)) hδbudget U position f

/-- One single geometric profile works for the actual cutoff-volume-indexed
family, provided its Wilson RG perturbation bound has been established for
every scale and every regulator, with the correct dual cocycle orientation. -/
theorem dual_source_wilson_geometric_all_regulators
    {Regulator : Type*}
    (A B : Regulator → ℕ → RootFiber21 → RootFiber21 → ℂ)
    (D θ : ℝ) (hD0 : 0 ≤ D) (hDhalf : D ≤ 1 / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hrow : ∀ (i : Regulator) (n : ℕ) (β : RootFiber21),
      (∑ j : RootFiber21, ‖A i n β j‖) ≤ D * θ ^ n)
    (hinv : ∀ i n, DualSourceInverse (A i n) (B i n))
    (U : Regulator → RootFiber21 → YMUICV128.Section03.SU2)
    (position : Regulator → RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ i n, ‖mixedWilsonDirection (sourceCocycleChain (B i) n)
      (U i) (position i) f‖ ≤
        4 * Real.exp (2 * (D / (1 - θ))) *
          SchwartzMap.seminorm ℂ 0 0 f := by
  intro i n
  exact dual_source_wilson_geometric_rg (A i) (B i)
    D θ hD0 hDhalf hθ0 hθ1 (hrow i) (hinv i)
    (U i) (position i) f n

end YMUIC.Wilson
