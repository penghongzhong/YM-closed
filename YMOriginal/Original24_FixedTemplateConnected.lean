import YMOriginal.Original24_ConnectedRootDistance
import YMOriginal.Original24_ActualWilsonRootFamilySupport

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Fixed-complexity actual Wilson root support removes UV root-count loss

For the ORIGINAL C29 fixed-D bounded source class, the possible
external roots have finite Wilson-word complexity.  The exact
root-support cardinality is not an abstract Nroot: it is bounded by
M*(L+1), where M is the number of physically distinct CLOSED Wilson
loops and L is their maximal link count.  This lemma combines that
strictly checked actual-site geometry with the previously verified
two-root exponential-distance connected Ursell estimate.

Penrose and FP finite-height tree comparison remain named published
combinatorial inputs; no original R-history support dictionary is
claimed proved by this cardinality lemma.
-/

/-- Original24 fixed-template two-root connected bound with NO
regulator-dependent root-cardinality constant. -/
theorem original24_fixed_template_connected_distance
    {P T S Γ : Type*} [Fintype T] [Fintype S] [Fintype Γ]
    (N chi : ℕ)
    (base : PeriodicBlock N)
    (loops : Finset (ClosedLinkWalkAt (PeriodicBlock N) base))
    (L : ℕ)
    (hLen : ∀ w ∈ loops, w.vertices.length ≤ L)
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
        actualPeriodicFirstRootSum N chi
          (actualFiniteWilsonRootFamilyBlocks base loops)
          support z d cGeo mu n) :
    Summable (fun n =>
      actualTwoRootInsertion U wp cp wq cq s t * Phi n) ∧
    (∑' n, ‖actualTwoRootInsertion U wp cp wq cq s t * Phi n‖) ≤
      ((Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)) *
      (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        ((loops.card * (L + 1) : ℕ) : ℝ)) * aAct) *
          Real.exp (-mu * dRoot) := by
  let root := actualFiniteWilsonRootFamilyBlocks base loops
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  let Nc : ℝ := (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ)
  have hp0' : 0 ≤ Real.exp (radius * Bp) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hq0' : 0 ≤ Real.exp (radius * Bq) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hp0' hq0'
  have hRootCard :=
    actual_finite_wilson_root_family_card base loops L hLen
  have hCardR :
      (root.card : ℝ) ≤ ((loops.card * (L + 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hRootCard
  have hRootBudget :
      (Nc * (root.card : ℝ)) * aAct ≤
      (Nc * ((loops.card * (L + 1) : ℕ) : ℝ)) * aAct := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCardR (by positivity)) ha
  have hFinal :
      K * ((Nc * (root.card : ℝ)) * aAct) *
        Real.exp (-mu * dRoot) ≤
      K * ((Nc * ((loops.card * (L + 1) : ℕ) : ℝ)) * aAct) *
        Real.exp (-mu * dRoot) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hRootBudget hK
  obtain ⟨hSummable, hBound⟩ :=
    original24_two_root_connected_distance
      N chi root support z d
      kappa mu cGeo aAct dRoot ha hdelta hsize hsmall hLocalNorm
      U wp cp wq cq s t radius Bp Bq
      hr hp0 hq0 hs ht hp hq
      Phi labeledTree hPenroseDistance hFP
  refine ⟨hSummable, ?_⟩
  exact hBound.trans hFinal

end YMUIC.Original24
