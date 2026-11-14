import YM.Wilson.SourceCocycleChain21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- The exact **dual inverse-transpose** matrix equation on the 21-dimensional
fixed-root source fiber.  If `A` is the primal relative RG perturbation, the
equation is `(I + Aᵀ) B = I`.  It does not assume a bound on B. -/
def DualSourceInverse (A B : RootFiber21 → RootFiber21 → ℂ) : Prop :=
  ∀ j α : RootFiber21,
    sourceCocycleCompose
      (fun j β => sourceCocycleIdentity j β + A β j) B j α =
        sourceCocycleIdentity j α

/-- Derive the exact fixed point identity for the inverse-transpose source
matrix from the original dual inverse matrix equation, not from a bound. -/
theorem dual_source_inverse_fixed_point
    (A B : RootFiber21 → RootFiber21 → ℂ)
    (hinv : DualSourceInverse A B) (j α : RootFiber21) :
    B j α + ∑ β : RootFiber21, A β j * B β α =
      sourceCocycleIdentity j α := by
  classical
  have h := hinv j α
  change (∑ β : RootFiber21,
    (sourceCocycleIdentity j β + A β j) * B β α) =
      sourceCocycleIdentity j α at h
  simp_rw [add_mul] at h
  rw [Finset.sum_add_distrib] at h
  have hid : (∑ β : RootFiber21,
      sourceCocycleIdentity j β * B β α) = B j α := by
    simp [sourceCocycleIdentity]
  simpa only [hid] using h

/-- The actual inverse-transpose matrix column norm follows from **primal
row control**.  The direction of the row/column requirement is crucial:
the source coordinates in the paper transform by `Z^{-T}`, not by `Z`.
No inverse norm estimate appears as a theorem parameter. -/
theorem dual_source_inverse_column_bound
    (A B : RootFiber21 → RootFiber21 → ℂ)
    (δ : ℝ) (hδ : δ < 1)
    (hrow : ∀ β : RootFiber21, (∑ j : RootFiber21, ‖A β j‖) ≤ δ)
    (hinv : DualSourceInverse A B) :
    ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖B j α‖) ≤ 1 / (1 - δ) := by
  classical
  intro α
  have hpoint (j : RootFiber21) :
      ‖B j α‖ ≤
        ‖sourceCocycleIdentity j α‖ +
          ∑ β : RootFiber21, ‖A β j‖ * ‖B β α‖ := by
    have hf := dual_source_inverse_fixed_point A B hinv j α
    have heq : B j α =
        sourceCocycleIdentity j α -
          (∑ β : RootFiber21, A β j * B β α) := by
      calc
        B j α = (B j α + ∑ β : RootFiber21, A β j * B β α) -
            ∑ β : RootFiber21, A β j * B β α := by ring
        _ = sourceCocycleIdentity j α -
            ∑ β : RootFiber21, A β j * B β α := by rw [hf]
    rw [heq]
    calc
      _ ≤ ‖sourceCocycleIdentity j α‖ +
            ‖∑ β : RootFiber21, A β j * B β α‖ := norm_sub_le _ _
      _ ≤ ‖sourceCocycleIdentity j α‖ +
            ∑ β : RootFiber21, ‖A β j * B β α‖ := by
        have ht : ‖∑ β : RootFiber21, A β j * B β α‖ ≤
            ∑ β : RootFiber21, ‖A β j * B β α‖ := norm_sum_le _ _
        exact add_le_add_right ht _
      _ = _ := by simp only [norm_mul]
  let S : ℝ := ∑ j : RootFiber21, ‖B j α‖
  have hbudget : S ≤ 1 + δ * S := by
    calc
      S ≤ ∑ j : RootFiber21,
          (‖sourceCocycleIdentity j α‖ +
            ∑ β : RootFiber21, ‖A β j‖ * ‖B β α‖) := by
        exact Finset.sum_le_sum (fun j hj => hpoint j)
      _ = (∑ j : RootFiber21, ‖sourceCocycleIdentity j α‖) +
          ∑ β : RootFiber21, (∑ j : RootFiber21, ‖A β j‖) *
            ‖B β α‖ := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ ≤ 1 + ∑ β : RootFiber21, δ * ‖B β α‖ := by
        rw [source_cocycle_identity_column]
        have ht : (∑ β : RootFiber21,
            (∑ j : RootFiber21, ‖A β j‖) * ‖B β α‖) ≤
            ∑ β : RootFiber21, δ * ‖B β α‖ := by
          apply Finset.sum_le_sum
          intro β hβ
          exact mul_le_mul_of_nonneg_right (hrow β) (norm_nonneg _)
        exact add_le_add_right ht 1
      _ = 1 + δ * S := by rw [Finset.mul_sum]
  have hpos : 0 < 1 - δ := by linarith
  apply (le_div_iff₀ hpos).mpr
  dsimp [S] at hbudget ⊢
  nlinarith [hbudget]

/-- The correct one-step **dual** source amplification follows from a
near-identity bound `‖A‖_(row ℓ¹) ≤ δ ≤ 1/2`, without assuming an inverse
bound.  The multiplier is `1 + 2δ`, not the raw matrix's `1+δ`. -/
theorem dual_source_inverse_one_step
    (A B : RootFiber21 → RootFiber21 → ℂ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hrow : ∀ β : RootFiber21, (∑ j : RootFiber21, ‖A β j‖) ≤ δ)
    (hinv : DualSourceInverse A B) :
    ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖B j α‖) ≤ 1 + 2 * δ := by
  have hδ : δ < 1 := by linarith
  have hpos : 0 < 1 - δ := by linarith
  have hq : 0 ≤ δ * (1 - 2 * δ) :=
    mul_nonneg hδ0 (by linarith)
  intro α
  calc
    _ ≤ 1 / (1 - δ) :=
      dual_source_inverse_column_bound A B δ hδ hrow hinv α
    _ ≤ 1 + 2 * δ := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith [hq]

end YMUIC.Wilson
