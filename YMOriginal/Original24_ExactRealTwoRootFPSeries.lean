import YMOriginal.Original24_DoubleFugacityFPTerminal
import YMOriginal.Original24_ExactExtendedWeighted
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# C29 Original24: literal connected TWO ROOT Wilson–Mayer full series

The ORIGINAL Mayer coefficient is now the actual graph on
  Sum (Fin n) (Fin 2)
with n bulk labels, exactly TWO independent root vertices, no
root-root bond, and the exact 1/n! labeled-graph symmetry factor.
The actual positive majorant is exactExtendedTwoRootTreeMajorant,
not an unverified, arbitrary Tree-indexed nonnegative sequence.

The ONLY remaining external FP input in this theorem is an actual
specified FINITE-HEIGHT tree-enumeration comparison, at the n+2
physical graph level. It maps the positive sum of exact root
spanning-tree counts to the already-built q-augmented positive KP
root forest. A height h includes at most h-2 physical bulk labels;
this is the required correction for the two external graph vertices.

The theorem then derives from REAL U1 smallness:
 * complete connected sum absolute convergence,
 * the exact marked true SU2 Wilson source bound,
 * a SMALL O(aAct) factor, uniformly for all truncation lengths.
No final two-root sum bound, no arbitrary Ursell Phi_n, no already
summable connected series and no post-R source analyticity is passed
as an assumption.

IMPORTANT: The external finite-height FP estimate for the exact
physical graph and the CMP119/122 R-history identification remain
unproved; this is a strict conditional theorem, not yet the original
manuscript B11 original environment #24.
-/

/-- The genuine positive full n+2-vertex Penrose tree majorant is
nonnegative for every actual finite periodic SU2 polymer model.
This is a property of the literal graph definition, not hFP. -/
theorem actual_exact_two_root_positive_tree_weight
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    0 ≤ exactExtendedTwoRootTreeMajorant
      n N chi rootP rootQ support z := by
  classical
  unfold exactExtendedTwoRootTreeMajorant
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro tuple ht
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg (fun i hi => norm_nonneg _))
  · exact le_refl 0

/-- A precise PHYSICAL finite-height FP comparison (still the
outstanding published-to-model combinatorial specialization):
the left side sums only actual TWO-root n+2-vertex spanning trees,
with correct n! and with at least one physical bulk polymer.

The weighted root q can occur at ANY vertex degree. The augmented
KP recursion is evaluated at sufficient height h to cover h-2
bulk-history labels. This premise is not the desired final bound. -/
def PhysicalExactTwoRootFPCriterion
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu : ℝ) : Prop :=
  ∀ lam eps : ℝ, ∀ h : ℕ, 1 ≤ lam → 0 < eps →
    (∑ k ∈ Finset.range (h - 2),
      (exactExtendedTwoRootTreeMajorant
        (k + 1) N chi rootP rootQ support z) *
        lam ^ (k + 1) * eps) ≤
    Real.exp (actualPeriodicFirstRootSum N chi rootP
      (actualSecondRootAugmentedSupport N support rootQ)
      (actualSecondRootAugmentedActivity
        (fun X => (lam : ℂ) * z X) eps)
      (actualSecondRootAugmentedSize d rootQ.card)
      cGeo mu h) - 1

/-- ACTUAL connected two-root Mayer coefficients and genuine bounded
Wilson-word source have an absolutely summable infinite series, with
a physical O(aAct) first-root gain.  The external combinatorial
input hFP now refers to EXACT physical labeled graph coefficient
and fixed root supports, not arbitrary abstract Tree values.

All n>=1 connected terms are accounted for. The n=0 term is
identically zero from the no-root--root edge theorem; see
Original24_ExactTwoRootAttachment.lean. -/
theorem actual_original24_two_root_mayer_full_sum_from_U1_FP
    (Pub : PublishedPenroseExtendedTwoRoot)
    {Γ P T S : Type*}
    [Fintype Γ] [Fintype T] [Fintype S]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (haAct : 0 < aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
        kappa - cGeo * mu)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct)
    (hFP : PhysicalExactTwoRootFPCriterion N chi
      rootP rootQ support z d cGeo mu)
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
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  have hkp : 0 ≤ Real.exp (radius * Bp) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hkq : 0 ≤ Real.exp (radius * Bq) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hkp hkq
  let w : ℕ → ℝ := fun n =>
    exactExtendedTwoRootTreeMajorant
      (n + 1) N chi rootP rootQ support z
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    exact actual_exact_two_root_positive_tree_weight
      (n + 1) N chi rootP rootQ support z
  have hFP' :
      ∀ (lam eps : ℝ) (h : ℕ), 1 ≤ lam → 0 < eps →
        (∑ n ∈ Finset.range (h - 2),
          w n * lam ^ (n + 1) * eps ^ (1 : ℕ)) ≤
        Real.exp
          (actualPeriodicFirstRootSum N chi rootP
            (actualSecondRootAugmentedSupport N support rootQ)
            (actualSecondRootAugmentedActivity
              (fun X => (lam : ℂ) * z X) eps)
            (actualSecondRootAugmentedSize d rootQ.card)
            cGeo mu h) - 1 := by
    intro lam eps h hlam heps
    simpa only [pow_one, w] using hFP lam eps h hlam heps
  obtain ⟨C, hC, htree⟩ :=
    original24_two_root_tree_O_aAct_from_U1_and_FP
      N chi rootP rootQ support z d
      kappa mu cGeo aAct haAct hdelta hsize hsmall hLocalNorm
      (fun h => Finset.range (h - 2))
      (fun n : ℕ => n + 1)
      (fun _n : ℕ => 1)
      w hw hFP'
  have htreePrefix (h : ℕ) :
      (∑ n ∈ Finset.range h, w n) ≤ C * aAct := by
    have hb := htree (h + 2)
    have hsub : h + 2 - 2 = h := by omega
    simpa only [hsub, Finset.mem_filter, Finset.mem_range,
      true_and, Nat.zero_le, and_true] using hb
  let term : ℕ → ℂ := fun n =>
    actualTwoRootInsertion U wp cp wq cq s t *
      actualExactTwoRootMayerTerm (n + 1) N chi
        rootP rootQ support z
  have hTerm (n : ℕ) : ‖term n‖ ≤ K * w n := by
    exact actual_exact_extended_marked_penrose
      Pub (n + 1) N chi rootP rootQ support z
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  have hprefix (h : ℕ) :
      (∑ n ∈ Finset.range h, ‖term n‖) ≤
        (K * C) * aAct := by
    calc
      _ ≤ ∑ n ∈ Finset.range h, K * w n :=
        Finset.sum_le_sum (fun n hn => hTerm n)
      _ = K * (∑ n ∈ Finset.range h, w n) := by
        rw [Finset.mul_sum]
      _ ≤ K * (C * aAct) :=
        mul_le_mul_of_nonneg_left (htreePrefix h) hK
      _ = (K * C) * aAct := by ring
  have hnorm : Summable (fun n : ℕ => ‖term n‖) :=
    summable_of_sum_range_le (fun n => norm_nonneg (term n)) hprefix
  have hsum : Summable term := summable_norm_iff.mp hnorm
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · exact hsum
  · exact hnorm
  · exact hnorm.tsum_le_of_sum_range_le hprefix

end YMUIC.Original24
