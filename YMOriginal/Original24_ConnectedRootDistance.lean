import YMOriginal.Original24_FromPublishedU1ConnectedFP
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24: restore the physical e^(-mu * dRoot) decay factor

The earlier connected-Ursell/FP assembly provided an all-height
rooted tree norm but did not yet record the original OFF-DIAGONAL
distance factor. Here the pointwise Penrose tree geometry explicitly
retains exp(mu*dRoot), while the already verified physical periodic
U1 -> U2 KP first-root recursion supplies the full tree budget.

The only combinatorial model inputs are the exact labeled Penrose
pointwise comparison and the FP finite-height tree-to-KP identity.
The infinite connected cluster summability, marked estimate, and
off-diagonal distance factor are outputs, never hypotheses.
-/

/-- Full connected cluster absolute convergence with the exact
e^(-mu*dRoot) factor, without assuming convergence or a completed
infinite tree bound. -/
theorem original24_connected_ursell_root_distance
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct dRoot : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct)
    (Phi : ℕ → ℂ)
    (labeledTree : ℕ → ℝ)
    (hPenroseDistance : ∀ n,
      Real.exp (mu * dRoot) * ‖Phi n‖ ≤ labeledTree n)
    (hFP : ∀ n,
      (∑ k ∈ Finset.range n, labeledTree k) ≤
        actualPeriodicFirstRootSum N chi root support z d cGeo mu n) :
    Summable Phi ∧ Summable (fun n => ‖Phi n‖) ∧
      (∑' n, ‖Phi n‖) ≤
        (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
           (root.card : ℝ)) * aAct) * Real.exp (-mu * dRoot) := by
  let M : ℝ :=
    ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (root.card : ℝ)) * aAct
  have hroot (n : ℕ) :
      actualPeriodicFirstRootSum N chi root support z d cGeo mu n ≤ M :=
    actual_periodic_first_root_uniform N chi root support z d
      kappa mu cGeo aAct ha hdelta hsize hsmall hLocalNorm n
  have hpref (n : ℕ) :
      (∑ k ∈ Finset.range n,
        Real.exp (mu * dRoot) * ‖Phi k‖) ≤ M := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, labeledTree k :=
        Finset.sum_le_sum (fun k hk => hPenroseDistance k)
      _ ≤ actualPeriodicFirstRootSum
        N chi root support z d cGeo mu n := hFP n
      _ ≤ M := hroot n
  have hsWeighted :
      Summable (fun n => Real.exp (mu * dRoot) * ‖Phi n‖) :=
    summable_of_sum_range_le
      (fun n => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      hpref
  have htsum :
      (∑' n, Real.exp (mu * dRoot) * ‖Phi n‖) ≤ M :=
    hsWeighted.tsum_le_of_sum_range_le hpref
  have hinv :
      Real.exp (-mu * dRoot) * Real.exp (mu * dRoot) = 1 := by
    rw [← Real.exp_add]
    have hzero : -mu * dRoot + mu * dRoot = 0 := by ring
    rw [hzero, Real.exp_zero]
  have heq (n : ℕ) :
      ‖Phi n‖ =
        Real.exp (-mu * dRoot) *
          (Real.exp (mu * dRoot) * ‖Phi n‖) := by
    rw [← mul_assoc, hinv, one_mul]
  have hfuneq :
      (fun n => ‖Phi n‖) =
        (fun n => Real.exp (-mu * dRoot) *
          (Real.exp (mu * dRoot) * ‖Phi n‖)) :=
    funext heq
  have hsNorm : Summable (fun n => ‖Phi n‖) := by
    rw [hfuneq]
    exact hsWeighted.mul_left _
  have hbound :
      (∑' n, ‖Phi n‖) ≤
        M * Real.exp (-mu * dRoot) := by
    calc
      (∑' n, ‖Phi n‖) =
          Real.exp (-mu * dRoot) *
            (∑' n, Real.exp (mu * dRoot) * ‖Phi n‖) := by
        rw [hfuneq, tsum_mul_left]
      _ ≤ Real.exp (-mu * dRoot) * M :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
      _ = M * Real.exp (-mu * dRoot) := by ring
  have hsPhi : Summable Phi := summable_norm_iff.mp hsNorm
  exact ⟨hsPhi, hsNorm, hbound⟩

/-- Two actual SU2 Wilson roots with the FULL arbitrary radius
now obtain the original off-diagonal rooted connected estimate:
  absolute connected sum <= K * Nroot * aAct * exp(-mu*dRoot).

No physical-source R-analyticity or connected-sum convergence is
included among the hypotheses. -/
theorem original24_two_root_connected_distance
    {P T S Γ : Type*} [Fintype T] [Fintype S] [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct dRoot : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct)
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (Phi : ℕ → ℂ) (labeledTree : ℕ → ℝ)
    (hPenroseDistance : ∀ n,
      Real.exp (mu * dRoot) * ‖Phi n‖ ≤ labeledTree n)
    (hFP : ∀ n,
      (∑ k ∈ Finset.range n, labeledTree k) ≤
        actualPeriodicFirstRootSum N chi root support z d cGeo mu n) :
    Summable (fun n =>
      actualTwoRootInsertion U wp cp wq cq s t * Phi n) ∧
    (∑' n,
      ‖actualTwoRootInsertion U wp cp wq cq s t * Phi n‖) ≤
      ((Real.exp (radius * Bp) - 1) *
         (Real.exp (radius * Bq) - 1)) *
      (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ)) * aAct) *
      Real.exp (-mu * dRoot) := by
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  have hKp : 0 ≤ Real.exp (radius * Bp) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hKq : 0 ≤ Real.exp (radius * Bq) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hKp hKq
  have hSrc : ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤ K :=
    actual_two_root_insertion_full_radius U wp cp wq cq
      s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  obtain ⟨hPhi, hNorm, hTotal⟩ :=
    original24_connected_ursell_root_distance
      N chi root support z d kappa mu cGeo aAct dRoot
      ha hdelta hsize hsmall hLocalNorm
      Phi labeledTree hPenroseDistance hFP
  have hsMarkedNorm : Summable (fun n =>
      ‖actualTwoRootInsertion U wp cp wq cq s t * Phi n‖) := by
    simp only [norm_mul]
    exact hNorm.mul_left _
  have hsMarked :
      Summable (fun n =>
        actualTwoRootInsertion U wp cp wq cq s t * Phi n) :=
    summable_norm_iff.mp hsMarkedNorm
  have hbound :
      (∑' n,
        ‖actualTwoRootInsertion U wp cp wq cq s t * Phi n‖) ≤
      K * (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ)) * aAct) * Real.exp (-mu * dRoot) := by
    calc
      (∑' n,
        ‖actualTwoRootInsertion U wp cp wq cq s t * Phi n‖) =
          ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
            (∑' n, ‖Phi n‖) := by
        simp only [norm_mul, tsum_mul_left]
      _ ≤ K * (∑' n, ‖Phi n‖) :=
        mul_le_mul_of_nonneg_right hSrc
          (tsum_nonneg (fun n => norm_nonneg _))
      _ ≤ K * (
        (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
            (root.card : ℝ)) * aAct) *
            Real.exp (-mu * dRoot)) :=
        mul_le_mul_of_nonneg_left hTotal hK
      _ = _ := by ring
  exact ⟨hsMarked, hbound⟩

end YMUIC.Original24
