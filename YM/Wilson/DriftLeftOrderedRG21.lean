import YM.Wilson.OrderedDualSourceRG21
import YM.Wilson.SourceDefect21
import YM.Wilson.InverseSquareBudget

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-!
# Correct chronological RG source residual with finite U3 drift budget

Unlike the earlier right-growing generic source chain, this uses the
paper's Z_n = R_(n-1) ... R_0.  Its scalar column norm is still bounded
by a finite product.  U3 drift pays any O(g_j^4) residual over the
actual finite weak-stop interval without assuming global Summable.
-/

theorem left_rg_prefix_column
    (R : ℕ → SourceRGMatrix21)
    (δ : ℕ → ℝ) (K : ℕ)
    (hδ : ∀ j < K, 0 ≤ δ j)
    (hstep : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖R j i α‖) ≤ 1 + δ j) :
    ∀ n : ℕ, n ≤ K → ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖leftOrderedSourceRGChain R n i α‖) ≤
        ∏ j ∈ Finset.range n, (1 + δ j) := by
  intro n
  induction n with
  | zero =>
      intro hn α
      simp [leftOrderedSourceRGChain, source_cocycle_identity_column]
  | succ n ih =>
      intro hn α
      have hnK : n < K := by omega
      have hnle : n ≤ K := by omega
      have hpos : 0 ≤ 1 + δ n := by linarith [hδ n hnK]
      have hb := source_cocycle_column_bound
        (R n) (leftOrderedSourceRGChain R n)
        (1 + δ n) (∏ j ∈ Finset.range n, (1 + δ j))
        hpos (hstep n hnK) (ih hnle) α
      change (∑ i : RootFiber21,
        ‖sourceCocycleCompose (R n) (leftOrderedSourceRGChain R n) i α‖) ≤
        ∏ j ∈ Finset.range (n + 1), (1 + δ j)
      calc
        _ ≤ (1 + δ n) *
            (∏ j ∈ Finset.range n, (1 + δ j)) := hb
        _ = ∏ j ∈ Finset.range (n + 1), (1 + δ j) := by
          rw [Finset.prod_range_succ]
          ring

/-- The finite nonnegative scalar RG budget is exponentiated without
post-stop hypotheses; a capped nonnegative sequence is used only inside
the proof of this inequality. -/
theorem weak_stop_prefix_product_exp
    (δ : ℕ → ℝ) (K : ℕ)
    (hδ : ∀ j < K, 0 ≤ δ j)
    (M : ℝ)
    (hsum : ∀ n ≤ K, (∑ j ∈ Finset.range n, δ j) ≤ M) :
    ∀ n : ℕ, n ≤ K →
      (∏ j ∈ Finset.range n, (1 + δ j)) ≤ Real.exp M := by
  intro n hn
  let δcap : ℕ → ℝ := fun j => if j < K then δ j else 0
  have hcap (j : ℕ) : 0 ≤ δcap j := by
    dsimp [δcap]
    by_cases hj : j < K
    · simp [hj]
      exact hδ j hj
    · simp [hj]
  have hsumcap :
      (∑ j ∈ Finset.range n, δcap j) =
        (∑ j ∈ Finset.range n, δ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjK : j < K := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    simp [δcap, hjK]
  have hprodcap :
      (∏ j ∈ Finset.range n, (1 + δcap j)) =
        (∏ j ∈ Finset.range n, (1 + δ j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjK : j < K := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    simp [δcap, hjK]
  calc
    (∏ j ∈ Finset.range n, (1 + δ j)) =
        ∏ j ∈ Finset.range n, (1 + δcap j) := hprodcap.symm
    _ ≤ Real.exp (∑ j ∈ Finset.range n, δcap j) :=
      Real.prod_one_add_le_exp_sum (Finset.range n) hcap
    _ = Real.exp (∑ j ∈ Finset.range n, δ j) := by rw [hsumcap]
    _ ≤ Real.exp M := Real.exp_le_exp.mpr (hsum n hn)

theorem left_rg_prefix_uniform
    (R : ℕ → SourceRGMatrix21)
    (δ : ℕ → ℝ) (K : ℕ)
    (hδ : ∀ j < K, 0 ≤ δ j)
    (hstep : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖R j i α‖) ≤ 1 + δ j)
    (M : ℝ)
    (hsum : ∀ n ≤ K, (∑ j ∈ Finset.range n, δ j) ≤ M) :
    ∀ n : ℕ, n ≤ K → ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖leftOrderedSourceRGChain R n i α‖) ≤
        Real.exp M := by
  intro n hn α
  exact (left_rg_prefix_column R δ K hδ hstep n hn α).trans
    (weak_stop_prefix_product_exp δ K hδ M hsum n hn)

/-- Actual U3 inverse-coupling arithmetic supplies the finite source
cocycle budget in the SAME order as manuscript C29 (304). -/
theorem drift_controlled_left_rg_uniform
    (R : ℕ → SourceRGMatrix21)
    (x : ℕ → ℝ) (K : ℕ)
    (xweak drift C : ℝ)
    (hxweak : 0 < xweak) (hdriftPos : 0 < drift) (hC : 0 ≤ C)
    (hlower : ∀ j ≤ K, xweak ≤ x j)
    (hstepX : ∀ j < K, drift ≤ x j - x (j + 1))
    (hresidual : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21,
        ‖R j i α - sourceCocycleIdentity i α‖) ≤
        C * ((x j)⁻¹ * (x j)⁻¹)) :
    ∀ n : ℕ, n ≤ K → ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖leftOrderedSourceRGChain R n i α‖) ≤
        Real.exp (C / (drift * xweak)) := by
  let δ : ℕ → ℝ := fun j => C * ((x j)⁻¹ * (x j)⁻¹)
  have hδ : ∀ j < K, 0 ≤ δ j := by
    intro j hj
    exact mul_nonneg hC (mul_self_nonneg _)
  have hcol : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖R j i α‖) ≤ 1 + δ j := by
    intro j hj α
    exact source_cocycle_step_from_identity_defect
      (R j) (δ j) (hresidual j hj) α
  have hsum (n : ℕ) (hn : n ≤ K) :
      (∑ j ∈ Finset.range n, δ j) ≤
        C / (drift * xweak) := by
    have hbase :=
      inverse_square_prefix_bound_ym
        x n xweak drift hxweak hdriftPos
        (fun j hj => hlower j (le_trans hj hn))
        (fun j hj => hstepX j (lt_of_lt_of_le hj hn))
    calc
      (∑ j ∈ Finset.range n, δ j) =
        C * (∑ j ∈ Finset.range n, (x j)⁻¹ * (x j)⁻¹) := by
          dsimp [δ]
          rw [Finset.mul_sum]
      _ ≤ C * (1 / (drift * xweak)) :=
        mul_le_mul_of_nonneg_left hbase hC
      _ = C / (drift * xweak) := by ring
  exact left_rg_prefix_uniform
    R δ K hδ hcol (C / (drift * xweak)) hsum

end YMUIC.Wilson
