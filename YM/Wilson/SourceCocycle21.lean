import YM.Wilson.SourceMix21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- Matrix action of two successive 21-dimensional source basis changes.
It is explicitly the **same root-fiber** composition B·C. -/
def sourceCocycleCompose
    (B C : RootFiber21 → RootFiber21 → ℂ) :
    RootFiber21 → RootFiber21 → ℂ :=
  fun j α => ∑ β : RootFiber21, B j β * C β α

/-- The column ℓ¹ amplification constant is submultiplicative for genuine
21×21 source matrices. This proof uses only finite-sum triangle inequality,
no assumed operator-norm result or Wilson source hypothesis. -/
theorem source_cocycle_column_bound
    (B C : RootFiber21 → RootFiber21 → ℂ)
    (KB KC : ℝ) (hKB : 0 ≤ KB)
    (hB : ∀ β : RootFiber21, (∑ j : RootFiber21, ‖B j β‖) ≤ KB)
    (hC : ∀ α : RootFiber21, (∑ β : RootFiber21, ‖C β α‖) ≤ KC) :
    ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖sourceCocycleCompose B C j α‖) ≤ KB * KC := by
  intro α
  calc
    (∑ j : RootFiber21, ‖sourceCocycleCompose B C j α‖) =
        ∑ j : RootFiber21, ‖∑ β : RootFiber21, B j β * C β α‖ := rfl
    _ ≤ ∑ j : RootFiber21,
        ∑ β : RootFiber21, ‖B j β * C β α‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sum_le _ _
    _ = ∑ β : RootFiber21,
        ∑ j : RootFiber21, ‖B j β‖ * ‖C β α‖ := by
      simp_rw [norm_mul]
      rw [Finset.sum_comm]
    _ = ∑ β : RootFiber21,
        (∑ j : RootFiber21, ‖B j β‖) * ‖C β α‖ := by
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ β : RootFiber21, KB * ‖C β α‖ := by
      apply Finset.sum_le_sum
      intro β hβ
      exact mul_le_mul_of_nonneg_right (hB β) (norm_nonneg _)
    _ = KB * (∑ β : RootFiber21, ‖C β α‖) := by
      rw [Finset.mul_sum]
    _ ≤ KB * KC := mul_le_mul_of_nonneg_left (hC α) hKB

/-- The nested action of two *actual* source mixing matrices is their
explicit product on the original plaquette-root Schwartz test directions.
This closes the algebraic source-cocycle dictionary, not the RG bound. -/
theorem mixed_wilson_cocycle_action
    (B C : RootFiber21 → RootFiber21 → ℂ)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    mixedWilsonDirection (sourceCocycleCompose B C) U position f =
      fun α => ∑ β : RootFiber21,
        C β α * mixedWilsonDirection B U position f β := by
  funext α
  calc
    mixedWilsonDirection (sourceCocycleCompose B C) U position f α =
        ∑ j : RootFiber21,
          (∑ β : RootFiber21, B j β * C β α) *
            wilsonPlaquetteDirection U position f j := rfl
    _ = ∑ j : RootFiber21,
        ∑ β : RootFiber21,
          (B j β * C β α) * wilsonPlaquetteDirection U position f j := by
      simp_rw [Finset.sum_mul]
    _ = ∑ β : RootFiber21,
        ∑ j : RootFiber21,
          C β α * (B j β * wilsonPlaquetteDirection U position f j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro β hβ
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ β : RootFiber21,
        C β α * (∑ j : RootFiber21,
          B j β * wilsonPlaquetteDirection U position f j) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ β : RootFiber21,
        C β α * mixedWilsonDirection B U position f β := rfl

/-- Concrete propagation of the Wilson source bound through **two** RG
source-cocycle steps, with no new factorial or root-count loss. -/
theorem mixed_wilson_two_step_uniform
    (B C : RootFiber21 → RootFiber21 → ℂ)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ)
    (KB KC : ℝ) (hKB : 0 ≤ KB) (hKC : 0 ≤ KC)
    (hB : ∀ β : RootFiber21, (∑ j : RootFiber21, ‖B j β‖) ≤ KB)
    (hC : ∀ α : RootFiber21, (∑ β : RootFiber21, ‖C β α‖) ≤ KC) :
    ‖mixedWilsonDirection (sourceCocycleCompose B C) U position f‖ ≤
      4 * (KB * KC) * SchwartzMap.seminorm ℂ 0 0 f := by
  exact mixed_wilson_direction_uniform (sourceCocycleCompose B C) U position
    f (KB * KC) (mul_nonneg hKB hKC)
    (source_cocycle_column_bound B C KB KC hKB hB hC)

end YMUIC.Wilson
