import YM.Wilson.CandidateGramSourceInsertion21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24 (C29 Theorem 15.5): actual composite SU(2) marked root bridge

Here the actual fixed-complexity candidate polynomial Wilson root,
not an abstract s-deformed R-operation, is inserted externally into
the original unmarked old/new-R polymer cluster sums.

The upstream U2 tree-weight majorant and its actual unmarked
old/new R bounds remain explicit premises. They are not replaced by
a direct bound on the desired marked output. Neither this component
nor its successful Lean compilation closes Original24 by itself:
the exact v111 template/canonical normalization, actual old/new
R graph/distance dictionary and B10 Taylor-localization still need
physical model identification.
-/

/-- One-root analogue of the already certified T007D rooted-tree sum.
The source amplitude K is kept exactly (no hidden polynomial loss). -/
theorem one_root_tree_sum
    {Γ : Type*}
    (φ treeWeight : Γ → ℝ)
    (K mu cRt dRoot aAct : ℝ)
    (Nroot : ℕ)
    (hφ : ∀ γ, 0 ≤ φ γ)
    (_htree : ∀ γ, 0 ≤ treeWeight γ)
    (hK : 0 ≤ K)
    (hweighted : ∀ γ,
      Real.exp (mu * dRoot) * φ γ ≤
        K * Real.exp (mu * cRt) * treeWeight γ)
    (hsum : Summable treeWeight)
    (htotal : (∑' γ, treeWeight γ) ≤ (Nroot : ℝ) * aAct) :
    (∑' γ, φ γ) ≤
      K * Real.exp (mu * cRt) * (Nroot : ℝ) *
        aAct * Real.exp (-mu * dRoot) := by
  let C : ℝ := K * Real.exp (mu * cRt) * Real.exp (-mu * dRoot)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint (γ : Γ) : φ γ ≤ C * treeWeight γ := by
    have h := mul_le_mul_of_nonneg_left
      (hweighted γ) (Real.exp_pos (-mu * dRoot)).le
    have hcancel :
        Real.exp (-mu * dRoot) * Real.exp (mu * dRoot) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      φ γ = (Real.exp (-mu * dRoot) *
          Real.exp (mu * dRoot)) * φ γ := by rw [hcancel, one_mul]
      _ = Real.exp (-mu * dRoot) *
          (Real.exp (mu * dRoot) * φ γ) := by ring
      _ ≤ Real.exp (-mu * dRoot) *
          (K * Real.exp (mu * cRt) * treeWeight γ) := h
      _ = C * treeWeight γ := by dsimp [C]; ring
  have hsumMaj : Summable (fun γ => C * treeWeight γ) :=
    hsum.mul_left C
  have hsumφ : Summable φ :=
    Summable.of_nonneg_of_le hφ hpoint hsumMaj
  calc
    (∑' γ, φ γ) ≤ ∑' γ, C * treeWeight γ :=
      hsumφ.tsum_le_tsum hpoint hsumMaj
    _ = C * (∑' γ, treeWeight γ) := tsum_mul_left
    _ ≤ C * ((Nroot : ℝ) * aAct) :=
      mul_le_mul_of_nonneg_left htotal hC
    _ = K * Real.exp (mu * cRt) * (Nroot : ℝ) *
          aAct * Real.exp (-mu * dRoot) := by
      dsimp [C]
      ring

/-- Actual candidate composite Wilson-polynomial external insertion
D(s)=exp(sO)-1 multiplied against *unmarked* R cluster activity. -/
def markedCompositeR
    {T Γ : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21)
    (coeff : T → ℂ)
    (s : ℂ) (unmarked : Γ → ℂ) (γ : Γ) : ℂ :=
  candidateGramSourceInsertion U monomials coeff s * unmarked γ

/-- The genuine exponential source bound (proved already from SU(2))
is propagated through the original U2 unmarked rooted-tree estimate.
No R(s) deformation is assumed anywhere. -/
theorem composite_r_marked_tree_sum
    {T Γ : Type*} [Fintype T]
    (U : GramPlaquette6 → SU2)
    (monomials : T → List RootFiber21)
    (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * candidateGramPolynomialBudget monomials coeff ≤ 1)
    (unmarked : Γ → ℂ) (treeWeight : Γ → ℝ)
    (mu cRt dRoot aAct : ℝ) (Nroot : ℕ)
    (htree : ∀ γ, 0 ≤ treeWeight γ)
    (hweighted : ∀ γ,
      Real.exp (mu * dRoot) * ‖unmarked γ‖ ≤
        Real.exp (mu * cRt) * treeWeight γ)
    (hsum : Summable treeWeight)
    (htotal : (∑' γ, treeWeight γ) ≤ (Nroot : ℝ) * aAct) :
    (∑' γ, ‖markedCompositeR U monomials coeff s unmarked γ‖) ≤
      (2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aAct * Real.exp (-mu * dRoot) := by
  let K : ℝ := 2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _))
      (candidate_gram_polynomial_budget_nonneg monomials coeff)
  have hD :
      ‖candidateGramSourceInsertion U monomials coeff s‖ ≤ K := by
    exact candidate_gram_insertion_small_source U monomials coeff s hsmall
  have hmarked (γ : Γ) :
      Real.exp (mu * dRoot) *
          ‖markedCompositeR U monomials coeff s unmarked γ‖ ≤
        K * Real.exp (mu * cRt) * treeWeight γ := by
    calc
      Real.exp (mu * dRoot) *
          ‖markedCompositeR U monomials coeff s unmarked γ‖ =
        ‖candidateGramSourceInsertion U monomials coeff s‖ *
          (Real.exp (mu * dRoot) * ‖unmarked γ‖) := by
          simp only [markedCompositeR, norm_mul]
          ring
      _ ≤ ‖candidateGramSourceInsertion U monomials coeff s‖ *
          (Real.exp (mu * cRt) * treeWeight γ) :=
        mul_le_mul_of_nonneg_left (hweighted γ) (norm_nonneg _)
      _ ≤ K * (Real.exp (mu * cRt) * treeWeight γ) :=
        mul_le_mul_of_nonneg_right hD
          (mul_nonneg (Real.exp_pos _).le (htree γ))
      _ = K * Real.exp (mu * cRt) * treeWeight γ := by ring
  exact one_root_tree_sum
    (fun γ => ‖markedCompositeR U monomials coeff s unmarked γ‖)
    treeWeight K mu cRt dRoot aAct Nroot
    (fun γ => norm_nonneg _) htree hK hmarked hsum htotal

/-- One theorem covers BOTH actual unmarked old-R and new-R sectors.
The source multipliers are identical; no new regulator-dependent source
analyticity hypothesis is introduced. -/
theorem composite_old_new_r_marked
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
    (hboundNew : (∑' γ, treeNew γ) ≤ (Nroot : ℝ) * aNew) :
    (∑' γ, ‖markedCompositeR U monomials coeff s oldR γ‖) ≤
      (2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aOld * Real.exp (-mu * dRoot) ∧
    (∑' γ, ‖markedCompositeR U monomials coeff s newR γ‖) ≤
      (2 * ‖s‖ * candidateGramPolynomialBudget monomials coeff) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aNew * Real.exp (-mu * dRoot) := by
  exact ⟨
    composite_r_marked_tree_sum U monomials coeff s hsmall
      oldR treeOld mu cRt dRoot aOld Nroot
      htreeOld hweightedOld hsumOld hboundOld,
    composite_r_marked_tree_sum U monomials coeff s hsmall
      newR treeNew mu cRt dRoot aNew Nroot
      htreeNew hweightedNew hsumNew hboundNew⟩

end YMUIC.Original24
