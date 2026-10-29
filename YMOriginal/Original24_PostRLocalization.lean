import YMOriginal.Original24_MarkedRootBridge

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24: actual marked Wilson source + B10 five-order post-R localization

The U2 rooted-tree step is proved in Original24_MarkedRootBridge.
The B10 fifth-order Taylor/placement entropy statement is an EXPLICIT
previous-paper input hB10, never inferred from mere root boundedness.
For the actual fixed composite SU(2) candidate root, prove here that
this B10 input and U2 source estimate give a genuinely summable
post-R localization remainder, uniformly over the number of RG layers.

The scalar q in (0,1) represents the paper's
  q = L^(-(1-theta)),
after multiplying the five-order gain by four-dimensional placement
entropy. Its concrete L/theta correspondence is still a model
dictionary to verify, NOT an unconditional new assumption about YM.
-/

/-- Real geometric-series closure with every finite-term bound explicit. -/
theorem finite_marked_remainder_geometric
    (q M : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (remainder : ℕ → ℂ)
    (hrem : ∀ m, ‖remainder m‖ ≤ M * q ^ m) :
    Summable (fun m => ‖remainder m‖) ∧
      (∑' m, ‖remainder m‖) ≤ M / (1 - q) := by
  have hmaj : Summable (fun m : ℕ => M * q ^ m) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left M
  have hsum : Summable (fun m : ℕ => ‖remainder m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hrem hmaj
  constructor
  · exact hsum
  · calc
      (∑' m, ‖remainder m‖) ≤ ∑' m : ℕ, M * q ^ m :=
        hsum.tsum_le_tsum hrem hmaj
      _ = M * (∑' m : ℕ, q ^ m) := tsum_mul_left
      _ = M * (1 - q)⁻¹ := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
      _ = M / (1 - q) := by ring

/-- Exact, numerically quantified post-R tail from actual composite SU(2)
marked old-R and new-R, using only the earlier B10 Taylor gain hB10
and the unmarked U2 rooted-tree bounds. The output is not a hypothesis. -/
theorem composite_old_new_post_r_localization_summable
    {T Γ : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21)
    (coeff : T → ℂ) (s : ℂ)
    (hsmall : ‖s‖ * candidateGramPolynomialBudget monomials coeff ≤ 1)
    (oldR newR : Γ → ℂ)
    (treeOld treeNew : Γ → ℝ)
    (mu cRt dRoot aOld aNew : ℝ) (Nroot : ℕ)
    (htreeOld : ∀ γ, 0 ≤ treeOld γ)
    (htreeNew : ∀ γ, 0 ≤ treeNew γ)
    (hweightedOld : ∀ γ,
      Real.exp (mu * dRoot) * ‖oldR γ‖ ≤
        Real.exp (mu * cRt) * treeOld γ)
    (hweightedNew : ∀ γ,
      Real.exp (mu * dRoot) * ‖newR γ‖ ≤
        Real.exp (mu * cRt) * treeNew γ)
    (hsumOld : Summable treeOld) (hsumNew : Summable treeNew)
    (hboundOld : (∑' γ, treeOld γ) ≤ (Nroot : ℝ) * aOld)
    (hboundNew : (∑' γ, treeNew γ) ≤ (Nroot : ℝ) * aNew)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (remainder : ℕ → ℂ)
    (hB10 : ∀ m, ‖remainder m‖ ≤
      ((∑' γ, ‖markedCompositeR U monomials coeff s oldR γ‖) +
        (∑' γ, ‖markedCompositeR U monomials coeff s newR γ‖)) *
          q ^ m) :
    Summable (fun m => ‖remainder m‖) ∧
      (∑' m, ‖remainder m‖) ≤
        ((2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff) *
        Real.exp (mu * cRt) * (Nroot : ℝ) *
        (aOld + aNew) * Real.exp (-mu * dRoot)) / (1 - q) := by
  let K : ℝ := 2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff
  let M : ℝ :=
    K * Real.exp (mu * cRt) * (Nroot : ℝ) *
      (aOld + aNew) * Real.exp (-mu * dRoot)
  obtain ⟨hOld, hNew⟩ :=
    composite_old_new_r_marked U monomials coeff s hsmall
      oldR newR treeOld treeNew mu cRt dRoot aOld aNew Nroot
      htreeOld htreeNew hweightedOld hweightedNew
      hsumOld hsumNew hboundOld hboundNew
  have hboth :
      (∑' γ, ‖markedCompositeR U monomials coeff s oldR γ‖) +
        (∑' γ, ‖markedCompositeR U monomials coeff s newR γ‖)
        ≤ M := by
    calc
      _ ≤
        (K * Real.exp (mu * cRt) * (Nroot : ℝ) * aOld *
          Real.exp (-mu * dRoot)) +
        (K * Real.exp (mu * cRt) * (Nroot : ℝ) * aNew *
          Real.exp (-mu * dRoot)) :=
          add_le_add hOld hNew
      _ = M := by dsimp [M, K]; ring
  have hrem (m : ℕ) : ‖remainder m‖ ≤ M * q ^ m :=
    (hB10 m).trans
      (mul_le_mul_of_nonneg_right hboth (pow_nonneg hq0 _))
  simpa only [M, K] using
    finite_marked_remainder_geometric q M hq0 hq1 remainder hrem

end YMUIC.Original24
