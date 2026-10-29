import YM.Wilson.SourceCocycleChain21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- No assumed source-operator norm: the actual column-one-step bound is
derived from the entrywise difference from the identity on the same
21-dimensional Wilson root fiber. -/
theorem source_cocycle_step_from_identity_defect
    (C : RootFiber21 → RootFiber21 → ℂ) (δ : ℝ)
    (hdefect : ∀ α : RootFiber21,
      (∑ j : RootFiber21,
        ‖C j α - sourceCocycleIdentity j α‖) ≤ δ) :
    ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖C j α‖) ≤ 1 + δ := by
  intro α
  have hpoint (j : RootFiber21) :
      ‖C j α‖ ≤
        ‖C j α - sourceCocycleIdentity j α‖ +
          ‖sourceCocycleIdentity j α‖ := by
    have ht := norm_add_le (C j α - sourceCocycleIdentity j α)
      (sourceCocycleIdentity j α)
    simpa only [sub_add_cancel] using ht
  calc
    (∑ j : RootFiber21, ‖C j α‖) ≤
        ∑ j : RootFiber21,
          (‖C j α - sourceCocycleIdentity j α‖ +
            ‖sourceCocycleIdentity j α‖) := by
              apply Finset.sum_le_sum
              intro j hj
              exact hpoint j
    _ = (∑ j : RootFiber21, ‖C j α - sourceCocycleIdentity j α‖) +
          (∑ j : RootFiber21, ‖sourceCocycleIdentity j α‖) := by
            rw [Finset.sum_add_distrib]
    _ ≤ δ + 1 := by
      rw [source_cocycle_identity_column]
      exact add_le_add_left (hdefect α) 1
    _ = 1 + δ := by ring

/-- A *summable*, nonnegative exact one-step defect is automatically
bounded in every partial RG window. The uniform constant is the actual
series sum; it is not an extra numerical input. -/
theorem source_cocycle_defect_partial_sum
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hsum : Summable δ) :
    ∀ n, (∑ j ∈ Finset.range n, δ j) ≤ ∑' j : ℕ, δ j := by
  intro n
  exact hsum.sum_le_tsum (Finset.range n) (fun j hj => hδ j)

/-- One actual finite root fiber whose step matrices stay within summable
column-ℓ¹ distances of the identity has a regulator-independent cumulative
source bound. No global cocycle bound is a hypothesis. -/
theorem source_cocycle_from_summable_matrix_defects
    (C : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hsum : Summable δ)
    (hstepDefect : ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21,
        ‖C n j α - sourceCocycleIdentity j α‖) ≤ δ n) :
    ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖sourceCocycleChain C n j α‖) ≤
        Real.exp (∑' j : ℕ, δ j) := by
  exact source_cocycle_chain_uniform_column C δ hδ
    (fun n => source_cocycle_step_from_identity_defect (C n) (δ n)
      (hstepDefect n))
    (∑' j : ℕ, δ j) (source_cocycle_defect_partial_sum δ hδ hsum)

/-- Derived, actual SU(2) Wilson-root source estimate after an arbitrary
number of renormalization steps. The two nontrivial remaining MODEL
obligations are the true step-defect bound and its uniform summability. -/
theorem wilson_source_of_summable_matrix_defects
    (C : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hsum : Summable δ)
    (hstepDefect : ∀ n : ℕ, ∀ α : RootFiber21,
      (∑ j : RootFiber21,
        ‖C n j α - sourceCocycleIdentity j α‖) ≤ δ n)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n, ‖mixedWilsonDirection (sourceCocycleChain C n) U position f‖ ≤
      4 * Real.exp (∑' j : ℕ, δ j) * SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  exact mixed_wilson_direction_uniform (sourceCocycleChain C n) U position
    f (Real.exp (∑' j : ℕ, δ j))
    (Real.exp_pos _).le
    (source_cocycle_from_summable_matrix_defects C δ hδ hsum hstepDefect n)

/-- Even when UV cutoffs, volumes and Wilson backgrounds vary, the same
summable one-step source defect controls the whole family without a
regulator-dependent loss. -/
theorem wilson_source_regulator_uniform_of_summable_defects
    {Regulator : Type*}
    (C : Regulator → ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hsum : Summable δ)
    (hstepDefect : ∀ i n α,
      (∑ j : RootFiber21,
        ‖C i n j α - sourceCocycleIdentity j α‖) ≤ δ n)
    (U : Regulator → RootFiber21 → YMUICV128.Section03.SU2)
    (position : Regulator → RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ i n, ‖mixedWilsonDirection (sourceCocycleChain (C i) n)
      (U i) (position i) f‖ ≤
        4 * Real.exp (∑' j : ℕ, δ j) * SchwartzMap.seminorm ℂ 0 0 f := by
  intro i n
  exact wilson_source_of_summable_matrix_defects (C i) δ hδ hsum
    (hstepDefect i) (U i) (position i) f n

end YMUIC.Wilson
