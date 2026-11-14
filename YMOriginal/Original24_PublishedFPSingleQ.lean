import YMOriginal.Original24_ExactWeightedTreeComparison
import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
-- short chain: published single-q FP is consumed directly by the physical full-series theorem
-- polymer type pinned explicitly for the published interface
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Published Fernández--Procacci single-q enumeration interface

This is the exact external combinatorial use boundary needed after the
internal physical graph dictionary has already been proved.

The external statement is deliberately NOT the target two-root Yang--Mills
bound. It concerns the positive p-rooted tree family after q has been
adjoined as one distinguished polymer species. The internally proved
exact two-root weighted-tree comparison maps the literal C29 n+2-vertex
physical graph into this family.

The factor lam^n * eps marks n ordinary bulk vertices and exactly one q
vertex. The recursive right-hand side is the already kernel-checked
finite-height KP recursion. The sign condition 0 <= cGeo * mu is explicit.
-/

universe u

/-- Universal published rooted-tree enumeration, specialized only to the
finite single-q hard-core model. This is a typed external theorem
interface, not a custom axiom and not a Yang--Mills analytic estimate. -/
structure PublishedFernandezProcacciSingleQ
    (Γ : Type u) [Fintype Γ] : Prop where
  finiteHeightBound :
    ∀ (N chi : ℕ)
      (rootP rootQ : Finset (PeriodicBlock N))
      (support : Γ → Finset (PeriodicBlock N))
      (z : Γ → ℂ) (d : Γ → ℕ)
      (cGeo mu lam eps : ℝ) (h : ℕ),
      0 ≤ cGeo * mu →
      1 ≤ lam →
      0 < eps →
      (∑ k ∈ Finset.range (h - 2),
        actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps) ≤
      Real.exp
        (actualPeriodicFirstRootSum N chi rootP
          (actualSecondRootAugmentedSupport N support rootQ)
          (actualSecondRootAugmentedActivity
            (fun X => (lam : ℂ) * z X) eps)
          (actualSecondRootAugmentedSize d rootQ.card)
          cGeo mu h) - 1

/-- Pointwise weighted comparison after the exact physical graph
embedding.  Keeping this as a separate lemma avoids repeatedly unfolding
the full physical FP criterion during the finite-sum proof. -/
theorem published_single_q_weighted_term
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (lam eps : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps)
    (n : ℕ) :
    exactExtendedTwoRootTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps ≤
      actualSingleQWeightedTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps := by
  have htree :=
    original24_exact_two_root_weighted_tree_le_single_q
      n N chi rootP rootQ support z
  have hfactor : 0 ≤ lam ^ n * eps :=
    mul_nonneg (pow_nonneg hlam _) heps
  calc
    exactExtendedTwoRootTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps =
      exactExtendedTwoRootTreeMajorant
        n N chi rootP rootQ support z * (lam ^ n * eps) := by
          ring
    _ ≤ actualSingleQWeightedTreeMajorant
        n N chi rootP rootQ support z * (lam ^ n * eps) :=
      mul_le_mul_of_nonneg_right htree hfactor
    _ = actualSingleQWeightedTreeMajorant
        n N chi rootP rootQ support z * lam ^ n * eps := by
          ring

/-- Finite-height physical two-root tree sum is bounded by the
corresponding positive single-q sum. -/
theorem published_single_q_weighted_sum
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (lam eps : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps)
    (h : ℕ) :
    (∑ k ∈ Finset.range (h - 2),
      exactExtendedTwoRootTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps) ≤
    ∑ k ∈ Finset.range (h - 2),
      actualSingleQWeightedTreeMajorant
          (k + 1) N chi rootP rootQ support z *
          lam ^ (k + 1) * eps := by
  apply Finset.sum_le_sum
  intro k hk
  exact published_single_q_weighted_term
    N chi rootP rootQ support z lam eps hlam heps (k + 1)


/-- Direct published-FP version of the full physical two-root series theorem.
The only new work here is the finite-height physical FP criterion; the
full connected-series argument is reused from the already compiled
Original24 theorem. -/
theorem actual_original24_two_root_mayer_full_sum_from_published_FP
    {Γ P T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (Pub : PublishedPenroseExtendedTwoRoot)
    (FP : PublishedFernandezProcacciSingleQ Γ)
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (hgeom : 0 ≤ cGeo * mu)
    (haAct : 0 < aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
        kappa - cGeo * mu)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct)
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun n : ℕ =>
        actualTwoRootInsertion U wp cp wq cq s t *
          actualExactTwoRootMayerTerm
            (n + 1) N chi rootP rootQ support z) ∧
      Summable (fun n : ℕ =>
        ‖actualTwoRootInsertion U wp cp wq cq s t *
          actualExactTwoRootMayerTerm
            (n + 1) N chi rootP rootQ support z‖) ∧
      (∑' n : ℕ,
        ‖actualTwoRootInsertion U wp cp wq cq s t *
          actualExactTwoRootMayerTerm
            (n + 1) N chi rootP rootQ support z‖) ≤
      ((Real.exp (radius * Bp) - 1) *
         (Real.exp (radius * Bq) - 1)) * C * aAct := by
  have hFP : PhysicalExactTwoRootFPCriterion
      N chi rootP rootQ support z d cGeo mu := by
    intro lam eps h hlam heps
    have hs :=
      published_single_q_weighted_sum
        N chi rootP rootQ support z lam eps
        (le_trans (by norm_num) hlam) heps.le h
    have hpublished :=
      FP.finiteHeightBound N chi rootP rootQ support z d
        cGeo mu lam eps h hgeom hlam heps
    exact hs.trans hpublished
  exact actual_original24_two_root_mayer_full_sum_from_U1_FP
    Pub N chi rootP rootQ support z d
    kappa mu cGeo aAct haAct hdelta hsize hsmall hLocalNorm hFP
    U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq

#print axioms published_single_q_weighted_term
#print axioms published_single_q_weighted_sum
#print axioms actual_original24_two_root_mayer_full_sum_from_published_FP

end YMUIC.Original24
