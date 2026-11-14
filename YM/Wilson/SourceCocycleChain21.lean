import YM.Wilson.SourceCocycle21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- Identity basis transformation on the actual 21-dimensional root fiber. -/
def sourceCocycleIdentity :
    RootFiber21 → RootFiber21 → ℂ :=
  fun j α => if j = α then 1 else 0

theorem source_cocycle_identity_column (α : RootFiber21) :
    (∑ j : RootFiber21, ‖sourceCocycleIdentity j α‖) = 1 := by
  classical
  have hn (j : RootFiber21) :
      ‖sourceCocycleIdentity j α‖ = if j = α then (1 : ℝ) else 0 := by
    by_cases h : j = α <;> simp [sourceCocycleIdentity, h]
  simp [hn]

/-- Cumulative source transformation, with order fixed by the actual
ordered RG cocycle convention. No boundedness is built into this definition. -/
def sourceCocycleChain (C : ℕ → RootFiber21 → RootFiber21 → ℂ) :
    ℕ → RootFiber21 → RootFiber21 → ℂ
  | 0 => sourceCocycleIdentity
  | n + 1 => sourceCocycleCompose (sourceCocycleChain C n) (C n)

/-- Derive the cumulative root-fiber column bound from **per-step**
bounds. No cumulative source-norm estimate is a hypothesis. -/
theorem source_cocycle_chain_column
    (C : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hstep : ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖C n j α‖) ≤ 1 + δ n) :
    ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖sourceCocycleChain C n j α‖) ≤
        ∏ j ∈ Finset.range n, (1 + δ j) := by
  intro n
  induction n with
  | zero =>
      intro α
      simp [sourceCocycleChain, source_cocycle_identity_column]
  | succ n ih =>
      intro α
      have hprod : 0 ≤ ∏ j ∈ Finset.range n, (1 + δ j) :=
        Finset.prod_nonneg (fun j hj => by linarith [hδ j])
      have hb := source_cocycle_column_bound
        (sourceCocycleChain C n) (C n)
        (∏ j ∈ Finset.range n, (1 + δ j)) (1 + δ n)
        hprod ih (hstep n) α
      simpa only [sourceCocycleChain, Finset.prod_range_succ] using hb

/-- A summable RG source-cocycle deviation yields a cutoff-uniform bound
on the actual cumulative 21-dimensional source transformation. -/
theorem source_cocycle_chain_uniform_column
    (C : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hstep : ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖C n j α‖) ≤ 1 + δ n)
    (M : ℝ)
    (hsum : ∀ n, (∑ j ∈ Finset.range n, δ j) ≤ M) :
    ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖sourceCocycleChain C n j α‖) ≤
        Real.exp M := by
  intro n α
  calc
    (∑ j : RootFiber21, ‖sourceCocycleChain C n j α‖)
        ≤ ∏ j ∈ Finset.range n, (1 + δ j) :=
          source_cocycle_chain_column C δ hδ hstep n α
    _ ≤ Real.exp (∑ j ∈ Finset.range n, δ j) :=
      Real.prod_one_add_le_exp_sum (Finset.range n) (fun j => hδ j)
    _ ≤ Real.exp M := Real.exp_le_exp.mpr (hsum n)

/-- Concrete regulator-uniform Wilson-source norm under a **local RG step
deviation sum**, with no direct cumulative column-norm hypothesis. -/
theorem wilson_source_of_summable_cocycle
    (C : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hstep : ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖C n j α‖) ≤ 1 + δ n)
    (M : ℝ)
    (hsum : ∀ n, (∑ j ∈ Finset.range n, δ j) ≤ M)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n, ‖mixedWilsonDirection (sourceCocycleChain C n) U position f‖ ≤
      4 * Real.exp M * SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  exact mixed_wilson_direction_uniform (sourceCocycleChain C n) U position
    f (Real.exp M) (Real.exp_pos M).le
    (source_cocycle_chain_uniform_column C δ hδ hstep M hsum n)

end YMUIC.Wilson
