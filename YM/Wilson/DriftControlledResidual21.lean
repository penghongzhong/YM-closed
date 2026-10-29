import YM.Wilson.CandidateGramRoots21
import YM.Wilson.SourceDefect21
import Section03.T011E_InverseSquare_PrefixBound

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-!
# Finite weak-stop source RG: genuine corrected-clock budget

The official, already-verified U3 inverse-coupling drift input gives
  sum_{j<K} x_j^(-2) <= 1/(drift*x_weak).
Thus O(x_j^(-2)) = O(g_j^4) source residuals have a UNIFORM finite
weak-stop error budget. No infinite RG summability input is assumed.

The missing Yang--Mills model step is to prove that the actual 21x21
RENORMALIZED residual matrix is O(g_j^4) after the correct one-loop
normalization and to control the frame endpoints.
-/

/-- Finite prefix version of the already-verified column-cocycle product:
only the genuine RG steps j<K are assumed controlled. -/
theorem source_cocycle_chain_prefix_column
    (R : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (K : ℕ)
    (hδ : ∀ j < K, 0 ≤ δ j)
    (hstep : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖R j i α‖) ≤ 1 + δ j) :
    ∀ n : ℕ, n ≤ K → ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖sourceCocycleChain R n i α‖) ≤
        ∏ j ∈ Finset.range n, (1 + δ j) := by
  intro n
  induction n with
  | zero =>
      intro hn α
      simp [sourceCocycleChain, source_cocycle_identity_column]
  | succ n ih =>
      intro hn α
      have hnK : n < K := by omega
      have hnle : n ≤ K := by omega
      have hprod : 0 ≤ ∏ j ∈ Finset.range n, (1 + δ j) := by
        apply Finset.prod_nonneg
        intro j hj
        have hjK : j < K :=
          lt_trans (Finset.mem_range.mp hj) hnK
        linarith [hδ j hjK]
      have hb := source_cocycle_column_bound
        (sourceCocycleChain R n) (R n)
        (∏ j ∈ Finset.range n, (1 + δ j)) (1 + δ n)
        hprod (ih hnle) (hstep n hnK) α
      simpa only [sourceCocycleChain, Finset.prod_range_succ] using hb

/-- A finite-stop summable error budget gives a uniform RG prefix
estimate, with no control of undefined/post-stop source steps. -/
theorem source_cocycle_chain_prefix_uniform
    (R : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (δ : ℕ → ℝ) (K : ℕ)
    (hδ : ∀ j < K, 0 ≤ δ j)
    (hstep : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖R j i α‖) ≤ 1 + δ j)
    (M : ℝ)
    (hsum : ∀ n ≤ K, (∑ j ∈ Finset.range n, δ j) ≤ M) :
    ∀ n : ℕ, n ≤ K → ∀ α : RootFiber21,
      (∑ i : RootFiber21, ‖sourceCocycleChain R n i α‖) ≤
        Real.exp M := by
  intro n hn α
  let δcap : ℕ → ℝ := fun j => if j < K then δ j else 0
  have hδcap (j : ℕ) : 0 ≤ δcap j := by
    dsimp [δcap]
    by_cases hj : j < K
    · simp only [if_pos hj]
      exact hδ j hj
    · simp [hj]
  have hsumcap :
      (∑ j ∈ Finset.range n, δcap j) =
        (∑ j ∈ Finset.range n, δ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjK : j < K :=
      lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    simp [δcap, hjK]
  have hprodcap :
      (∏ j ∈ Finset.range n, (1 + δcap j)) =
        (∏ j ∈ Finset.range n, (1 + δ j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjK : j < K :=
      lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    simp [δcap, hjK]
  calc
    (∑ i : RootFiber21, ‖sourceCocycleChain R n i α‖) ≤
        ∏ j ∈ Finset.range n, (1 + δ j) :=
      source_cocycle_chain_prefix_column R δ K hδ hstep n hn α
    _ = ∏ j ∈ Finset.range n, (1 + δcap j) := hprodcap.symm
    _ ≤ Real.exp (∑ j ∈ Finset.range n, δcap j) :=
      Real.prod_one_add_le_exp_sum (Finset.range n) hδcap
    _ = Real.exp (∑ j ∈ Finset.range n, δ j) := by rw [hsumcap]
    _ ≤ Real.exp M := Real.exp_le_exp.mpr (hsum n hn)

/-- Corrected-clock drift pays for EVERY O(g_j^4) RG matrix residual
at a finite weak-stop horizon, using the existing strict U3 theorem.
There is no independent postulated summability or cumulative norm. -/
theorem drift_controlled_residual_cocycle_uniform
    (R : ℕ → RootFiber21 → RootFiber21 → ℂ)
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
      (∑ i : RootFiber21, ‖sourceCocycleChain R n i α‖) ≤
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
      YMUICV128.Section03.T011E.inverse_square_prefix_bound
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
  exact source_cocycle_chain_prefix_uniform
    R δ K hδ hcol (C / (drift * xweak)) hsum

/-- The actual candidate 21-component SU2 plaquette source inherits the
same uniform estimate on the genuine weak-stop interval. -/
theorem drift_controlled_candidate_source_uniform
    (R : ℕ → RootFiber21 → RootFiber21 → ℂ)
    (x : ℕ → ℝ) (K : ℕ)
    (xweak drift C : ℝ)
    (hxweak : 0 < xweak) (hdriftPos : 0 < drift) (hC : 0 ≤ C)
    (hlower : ∀ j ≤ K, xweak ≤ x j)
    (hstepX : ∀ j < K, drift ≤ x j - x (j + 1))
    (hresidual : ∀ j < K, ∀ α : RootFiber21,
      (∑ i : RootFiber21,
        ‖R j i α - sourceCocycleIdentity i α‖) ≤
        C * ((x j)⁻¹ * (x j)⁻¹))
    (U : GramPlaquette6 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n : ℕ, n ≤ K →
      ‖mixedCandidateGramSchwartz (sourceCocycleChain R n)
        U position f‖ ≤
      4 * Real.exp (C / (drift * xweak)) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  intro n hn
  exact mixed_candidate_gram_uniform (sourceCocycleChain R n)
    U position f (Real.exp (C / (drift * xweak)))
    (Real.exp_pos _).le
    (drift_controlled_residual_cocycle_uniform
      R x K xweak drift C hxweak hdriftPos hC
      hlower hstepX hresidual n hn)

end YMUIC.Wilson
