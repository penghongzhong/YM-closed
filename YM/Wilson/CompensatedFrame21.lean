import YM.Wilson.SourceDefect21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-!
An algebraic compensating-frame alternative to summability of the raw
21-dimensional Yang--Mills RG source matrices.

If the physical dual source step has a normalization/frame factorization
  C_n = F_n (I + E_n) F_{n+1}^{-1},
the potentially large/marginal frame factors telescope.  Only the residual
E_n must have a summable column defect.  This file DOES NOT assert that the
actual YM source cocycle admits such a factorization.
-/

abbrev SourceMatrix21 := Matrix RootFiber21 RootFiber21 ℂ

private theorem source_compose_as_mul (B C : SourceMatrix21) :
    sourceCocycleCompose B C = B * C := by
  ext j α
  simp [sourceCocycleCompose, Matrix.mul_apply]

private theorem source_identity_as_one :
    (sourceCocycleIdentity : SourceMatrix21) = 1 := by
  classical
  ext j α
  by_cases h : j = α <;> simp [sourceCocycleIdentity, h]

private theorem source_chain_succ_as_mul
    (C : ℕ → SourceMatrix21) (n : ℕ) :
    sourceCocycleChain C (n + 1) = (sourceCocycleChain C n : SourceMatrix21) * C n := by
  change sourceCocycleCompose (sourceCocycleChain C n) (C n) =
    (sourceCocycleChain C n : SourceMatrix21) * C n
  exact source_compose_as_mul _ _

/-- The actual finite 21-dimensional cocycle step, factored through a
scale-dependent source normalization and a residual RG matrix. -/
def compensatedSourceStep
    (F Finv R : ℕ → SourceMatrix21) (n : ℕ) : SourceMatrix21 :=
  F n * R n * Finv (n + 1)

/-- Exact telescoping of scale-dependent frames.  The only inverse facts
required are the displayed finite-matrix identities; no norm bound on
individual raw source steps C_n is needed. -/
theorem compensated_source_chain_factorization
    (F Finv R : ℕ → SourceMatrix21)
    (hleft : ∀ n, Finv n * F n = 1)
    (hright0 : F 0 * Finv 0 = 1) :
    ∀ n, sourceCocycleChain (compensatedSourceStep F Finv R) n =
      F 0 * (sourceCocycleChain R n : SourceMatrix21) * Finv n := by
  intro n
  induction n with
  | zero =>
      change (sourceCocycleIdentity : SourceMatrix21) =
        F 0 * (sourceCocycleIdentity : SourceMatrix21) * Finv 0
      rw [source_identity_as_one, Matrix.mul_one]
      exact hright0.symm
  | succ n ih =>
      rw [source_chain_succ_as_mul, ih, source_chain_succ_as_mul]
      change (F 0 * (sourceCocycleChain R n : SourceMatrix21) * Finv n) *
        (F n * R n * Finv (n + 1)) =
        F 0 * ((sourceCocycleChain R n : SourceMatrix21) * R n) * Finv (n + 1)
      calc
        _ = F 0 * (sourceCocycleChain R n : SourceMatrix21) *
            ((Finv n * F n) * R n) * Finv (n + 1) := by
              simp only [Matrix.mul_assoc]
        _ = F 0 * ((sourceCocycleChain R n : SourceMatrix21) * R n) *
            Finv (n + 1) := by
              rw [hleft n]
              simp only [Matrix.one_mul, Matrix.mul_assoc]

/-- A uniform bound can survive nonsummable raw one-step changes:
only the compensated residual defects must be summable, and the two
ENDPOINT frames must have uniform column norms.  The result does not
assume any cumulative RG cocycle bound. -/
theorem compensated_source_chain_uniform_column
    (F Finv R : ℕ → SourceMatrix21)
    (hleft : ∀ n, Finv n * F n = 1)
    (hright0 : F 0 * Finv 0 = 1)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hsum : Summable δ)
    (hresidual : ∀ (n : ℕ) (α : RootFiber21),
      (∑ j : RootFiber21,
        ‖R n j α - sourceCocycleIdentity j α‖) ≤ δ n)
    (KF KG : ℝ) (hKF : 0 ≤ KF) (hKG : 0 ≤ KG)
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
      (∑ j : RootFiber21, ‖sourceCocycleChain R n j β‖) ≤
        Real.exp (∑' j : ℕ, δ j) :=
    source_cocycle_from_summable_matrix_defects R δ hδ hsum
      hresidual n β
  have hFR (β : RootFiber21) :
      (∑ j : RootFiber21,
        ‖(F 0 * (sourceCocycleChain R n : SourceMatrix21)) j β‖) ≤
          KF * Real.exp (∑' j : ℕ, δ j) := by
    simpa only [source_compose_as_mul] using
      (source_cocycle_column_bound (F 0) (sourceCocycleChain R n)
        KF (Real.exp (∑' j : ℕ, δ j))
        hKF hF0 hR β)
  simpa only [source_compose_as_mul] using
    (source_cocycle_column_bound
      (F 0 * (sourceCocycleChain R n : SourceMatrix21)) (Finv n)
      (KF * Real.exp (∑' j : ℕ, δ j)) KG
      (mul_nonneg hKF (Real.exp_pos _).le)
      hFR (hG n) α)

/-- Apply the compensated RG bound to the genuine SU(2) plaquette-root
Schwartz source.  All RG step/model claims remain explicit inputs. -/
theorem compensated_wilson_source_uniform
    (F Finv R : ℕ → SourceMatrix21)
    (hleft : ∀ n, Finv n * F n = 1)
    (hright0 : F 0 * Finv 0 = 1)
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
