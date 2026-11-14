import YM.Wilson.DualSourceInverse21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- The correct finite-dimensional *dual* source RG chain with the exact
inverse-transpose relationship at every step. Stepwise **primal row**
deviations plus a summable error budget imply a regulator-independent
column bound for the complete dual source cocycle. -/
theorem dual_source_chain_uniform_column
    (A B : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n)
    (hδhalf : ∀ n, δ n ≤ 1 / 2)
    (hrow : ∀ (n : ℕ) (β : RootFiber21),
      (∑ j : RootFiber21, ‖A n β j‖) ≤ δ n)
    (hinv : ∀ n, DualSourceInverse (A n) (B n))
    (M : ℝ)
    (hsum : ∀ n, (∑ j ∈ Finset.range n, δ j) ≤ M) :
    ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖sourceCocycleChain B n j α‖) ≤
        Real.exp (2 * M) := by
  have hsum2 (n : ℕ) :
      (∑ j ∈ Finset.range n, 2 * δ j) ≤ 2 * M := by
    calc
      _ = 2 * (∑ j ∈ Finset.range n, δ j) := by
        simp only [Finset.mul_sum]
      _ ≤ 2 * M :=
        mul_le_mul_of_nonneg_left (hsum n) (by norm_num)
  exact source_cocycle_chain_uniform_column B (fun n => 2 * δ n)
    (fun n => mul_nonneg (by norm_num) (hδ0 n))
    (fun n α => dual_source_inverse_one_step
      (A n) (B n) (δ n) (hδ0 n) (hδhalf n)
      (hrow n) (hinv n) α)
    (2 * M) hsum2

/-- A source-regulator-uniform estimate at all RG scales for the **actual**
SU(2) Wilson plaquette root test and its correctly oriented dual cocycle.
The sum-of-small-perturbations estimate is still explicitly needed. -/
theorem dual_source_wilson_rg_uniform
    (A B : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n)
    (hδhalf : ∀ n, δ n ≤ 1 / 2)
    (hrow : ∀ (n : ℕ) (β : RootFiber21),
      (∑ j : RootFiber21, ‖A n β j‖) ≤ δ n)
    (hinv : ∀ n, DualSourceInverse (A n) (B n))
    (M : ℝ)
    (hsum : ∀ n, (∑ j ∈ Finset.range n, δ j) ≤ M)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n, ‖mixedWilsonDirection (sourceCocycleChain B n) U position f‖ ≤
      4 * Real.exp (2 * M) * SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  exact mixed_wilson_direction_uniform (sourceCocycleChain B n) U position
    f (Real.exp (2 * M)) (Real.exp_pos _).le
    (dual_source_chain_uniform_column A B δ hδ0 hδhalf
      hrow hinv M hsum n)

end YMUIC.Wilson
