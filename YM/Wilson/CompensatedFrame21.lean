import YM.Wilson.SourceDefect21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-!
# Wilson-source compensating frames (conditional algebra)

This module uses the existing finite source-cocycle composition directly,
rather than overloading multiplication of functions and matrices.

The actual YM model is NOT asserted to supply the frame decomposition,
the endpoint uniform norm estimates, or a summable residual source error.
-/

abbrev SourceMatrix21 := RootFiber21 → RootFiber21 → ℂ

private theorem source_compose_assoc (A B C : SourceMatrix21) :
    sourceCocycleCompose (sourceCocycleCompose A B) C =
      sourceCocycleCompose A (sourceCocycleCompose B C) := by
  classical
  funext j α
  simp only [sourceCocycleCompose]
  calc
    (∑ β : RootFiber21,
        (∑ γ : RootFiber21, A j γ * B γ β) * C β α) =
      ∑ β : RootFiber21, ∑ γ : RootFiber21,
        (A j γ * B γ β) * C β α := by
          simp_rw [Finset.sum_mul]
    _ = ∑ γ : RootFiber21, ∑ β : RootFiber21,
        (A j γ * B γ β) * C β α := by
          rw [Finset.sum_comm]
    _ = ∑ γ : RootFiber21, ∑ β : RootFiber21,
        A j γ * (B γ β * C β α) := by
          apply Finset.sum_congr rfl
          intro γ hγ
          apply Finset.sum_congr rfl
          intro β hβ
          ring
    _ = ∑ γ : RootFiber21,
        A j γ * (∑ β : RootFiber21, B γ β * C β α) := by
          simp_rw [Finset.mul_sum]

private theorem source_compose_left_id (B : SourceMatrix21) :
    sourceCocycleCompose sourceCocycleIdentity B = B := by
  classical
  funext j α
  simp [sourceCocycleCompose, sourceCocycleIdentity]

private theorem source_compose_right_id (B : SourceMatrix21) :
    sourceCocycleCompose B sourceCocycleIdentity = B := by
  classical
  funext j α
  simp [sourceCocycleCompose, sourceCocycleIdentity]

/-- Finite source RG step with the scale-dependent frame separated from
the residual source step. -/
def compensatedSourceStep (F Finv R : ℕ → SourceMatrix21)
    (n : ℕ) : SourceMatrix21 :=
  sourceCocycleCompose
    (sourceCocycleCompose (F n) (R n)) (Finv (n + 1))

/-- Exact telescoping with no matrix-norm assumption. -/
theorem compensated_source_chain_factorization
    (F Finv R : ℕ → SourceMatrix21)
    (hleft : ∀ n, sourceCocycleCompose (Finv n) (F n) =
        sourceCocycleIdentity)
    (hright0 : sourceCocycleCompose (F 0) (Finv 0) =
        sourceCocycleIdentity) :
    ∀ n, sourceCocycleChain (compensatedSourceStep F Finv R) n =
      sourceCocycleCompose
        (sourceCocycleCompose (F 0) (sourceCocycleChain R n))
        (Finv n) := by
  intro n
  induction n with
  | zero =>
      change sourceCocycleIdentity =
        sourceCocycleCompose
          (sourceCocycleCompose (F 0) sourceCocycleIdentity)
          (Finv 0)
      rw [source_compose_right_id]
      exact hright0.symm
  | succ n ih =>
      change sourceCocycleCompose
        (sourceCocycleChain (compensatedSourceStep F Finv R) n)
        (compensatedSourceStep F Finv R n) =
        sourceCocycleCompose
          (sourceCocycleCompose (F 0)
            (sourceCocycleCompose (sourceCocycleChain R n) (R n)))
          (Finv (n + 1))
      rw [ih]
      simp only [compensatedSourceStep, source_compose_assoc]
      rw [← source_compose_assoc (Finv n) (F n)
          (sourceCocycleCompose (R n) (Finv (n + 1))),
          hleft n, source_compose_left_id]

/-- Regulator-independent column bound follows from a summable residual
defect and endpoint frame control, WITHOUT assuming a cumulative raw source
norm.  The physical frame/defect hypotheses remain open in the YM model. -/
theorem compensated_source_chain_uniform_column
    (F Finv R : ℕ → SourceMatrix21)
    (hleft : ∀ n, sourceCocycleCompose (Finv n) (F n) =
        sourceCocycleIdentity)
    (hright0 : sourceCocycleCompose (F 0) (Finv 0) =
        sourceCocycleIdentity)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hsum : Summable δ)
    (hresidual : ∀ (n : ℕ) (α : RootFiber21),
      (∑ j : RootFiber21,
        ‖R n j α - sourceCocycleIdentity j α‖) ≤ δ n)
    (KF KG : ℝ) (hKF : 0 ≤ KF) (_hKG : 0 ≤ KG)
    (hF0 : ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖F 0 j α‖) ≤ KF)
    (hG : ∀ (n : ℕ) (α : RootFiber21),
      (∑ j : RootFiber21, ‖Finv n j α‖) ≤ KG) :
    ∀ (n : ℕ) (α : RootFiber21),
      (∑ j : RootFiber21,
        ‖sourceCocycleChain (compensatedSourceStep F Finv R) n j α‖)
          ≤ KF * Real.exp (∑' j : ℕ, δ j) * KG := by
  intro n α
  rw [compensated_source_chain_factorization F Finv R hleft hright0 n]
  have hR (β : RootFiber21) :
      (∑ j : RootFiber21, ‖sourceCocycleChain R n j β‖)
        ≤ Real.exp (∑' j : ℕ, δ j) :=
    source_cocycle_from_summable_matrix_defects R δ hδ hsum
      hresidual n β
  have hFR (β : RootFiber21) :
      (∑ j : RootFiber21,
        ‖sourceCocycleCompose (F 0) (sourceCocycleChain R n) j β‖)
          ≤ KF * Real.exp (∑' j : ℕ, δ j) :=
    source_cocycle_column_bound (F 0) (sourceCocycleChain R n)
      KF (Real.exp (∑' j : ℕ, δ j)) hKF hF0 hR β
  exact source_cocycle_column_bound
    (sourceCocycleCompose (F 0) (sourceCocycleChain R n))
    (Finv n) (KF * Real.exp (∑' j : ℕ, δ j)) KG
    (mul_nonneg hKF (Real.exp_pos _).le)
    hFR (hG n) α

/-- An actual SU(2) Wilson plaquette Schwartz test inherits the conditional
compensated-frame source bound. -/
theorem compensated_wilson_source_uniform
    (F Finv R : ℕ → SourceMatrix21)
    (hleft : ∀ n, sourceCocycleCompose (Finv n) (F n) =
        sourceCocycleIdentity)
    (hright0 : sourceCocycleCompose (F 0) (Finv 0) =
        sourceCocycleIdentity)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hsum : Summable δ)
    (hresidual : ∀ (n : ℕ) (α : RootFiber21),
      (∑ j : RootFiber21,
        ‖R n j α - sourceCocycleIdentity j α‖) ≤ δ n)
    (KF KG : ℝ) (hKF : 0 ≤ KF) (hKG : 0 ≤ KG)
    (hF0 : ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖F 0 j α‖) ≤ KF)
    (hG : ∀ (n : ℕ) (α : RootFiber21),
      (∑ j : RootFiber21, ‖Finv n j α‖) ≤ KG)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n, ‖mixedWilsonDirection
        (sourceCocycleChain (compensatedSourceStep F Finv R) n)
        U position f‖ ≤
      4 * (KF * Real.exp (∑' j : ℕ, δ j) * KG) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  exact mixed_wilson_direction_uniform
    (sourceCocycleChain (compensatedSourceStep F Finv R) n)
    U position f _
    (mul_nonneg (mul_nonneg hKF (Real.exp_pos _).le) hKG)
    (compensated_source_chain_uniform_column
      F Finv R hleft hright0 δ hδ hsum hresidual
      KF KG hKF hKG hF0 hG n)

end YMUIC.Wilson
