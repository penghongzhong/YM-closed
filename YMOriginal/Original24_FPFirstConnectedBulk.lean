import YMOriginal.Original24_ExactWeightedTreeComparison
import YMOriginal.Original24_OnePolymerTwoRootReal
import YMOriginal.Original24_ExactAugmentedQContact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original24: genuine first nonzero n=1 contribution to the FP sum

For one actual bulk polymer contacting both source roots, q is a
genuine augmented KP child of that bulk polymer.  The all-height
finite KP recursion therefore produces the correct lambda*epsilon
coefficient without any physical hFP, positive-tree count, or
postulated connected cluster norm.  The required physical sign
condition 0 <= cGeo*mu is recorded explicitly: the unweighted
Mayer weights cannot be bounded by negatively weighted KP trees.
-/

/-- The q-augmented finite-height rooted recursion dominates the
entire one-bulk/two-external-root contact contribution already at
one nontrivial tree-generation step.

The left side uses ACTUAL 4D periodic p-X-q source connections,
the unmodified SU2 polymer activity z, and exact fugacities
lambda and epsilon.  No version of PhysicalExactTwoRootFPCriterion,
Penrose identity, full tree enumeration, or RG norm estimate is a
hypothesis. The theorem is the genuine first coefficient of the
eventual all-n finite-height FP statement, not that statement itself. -/
theorem original24_FP_one_bulk_connected_from_KP
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu lam eps : ℝ)
    (hgeom : 0 ≤ cGeo * mu)
    (hlam : 1 ≤ lam) (heps : 0 < eps)
    (h : ℕ) :
    (∑ X ∈ actualOnePolymerTwoRootBridge N chi rootP rootQ support,
       lam * eps * ‖z X‖) ≤
    Real.exp
      (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity
          (fun X => (lam : ℂ) * z X) eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu (h + 1)) - 1 := by
  classical
  let supp : Sum Γ Unit → Finset (PeriodicBlock N) :=
    actualSecondRootAugmentedSupport N support rootQ
  let act : Sum Γ Unit → ℂ :=
    actualSecondRootAugmentedActivity
      (fun X => (lam : ℂ) * z X) eps
  let sz : Sum Γ Unit → ℕ :=
    actualSecondRootAugmentedSize d rootQ.card
  let w : Sum Γ Unit → ℝ :=
    fun Y => ‖act Y‖ * Real.exp ((cGeo * mu) * (sz Y : ℝ))
  let H : ℕ → Sum Γ Unit → ℝ :=
    actualPeriodicTreeHeight N chi supp w
  let Q : Sum Γ Unit := Sum.inr ()
  let A := actualOnePolymerTwoRootBridge N chi rootP rootQ support
  let R := actualContactRoot rootP
    (fourDimPeriodicNeighborhood N chi) supp
  let F : ℝ :=
    actualPeriodicFirstRootSum N chi rootP supp act sz cGeo mu (h + 1)
  have hlam0 : 0 ≤ lam := by linarith
  have heps0 : 0 ≤ eps := heps.le
  have hw : ∀ Y, 0 ≤ w Y := by
    intro Y
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hFone : ∀ k Y, 1 ≤ H k Y := by
    intro k
    induction k with
    | zero =>
        intro Y
        change (1 : ℝ) ≤ 1
        exact le_rfl
    | succ k ih =>
        intro Y
        change (1 : ℝ) ≤
          Real.exp (∑ Z ∈ actualPeriodicPolymerChildren N chi supp Y,
            w Z * H k Z)
        apply Real.one_le_exp_iff.mpr
        apply Finset.sum_nonneg
        intro Z hZ
        exact mul_nonneg (hw Z) (by linarith [ih Z])
  have hqWeight : eps ≤ w Q := by
    have he : 1 ≤ Real.exp ((cGeo * mu) * (rootQ.card : ℝ)) :=
      Real.one_le_exp_iff.mpr
        (mul_nonneg hgeom (Nat.cast_nonneg _))
    change eps ≤ ‖(eps : ℂ)‖ *
      Real.exp ((cGeo * mu) * (rootQ.card : ℝ))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg heps0]
    calc
      eps = eps * 1 := by ring
      _ ≤ eps * Real.exp ((cGeo * mu) * (rootQ.card : ℝ)) :=
        mul_le_mul_of_nonneg_left he heps0
  have hbulkWeight (X : Γ) : lam * ‖z X‖ ≤ w (Sum.inl X) := by
    have he : 1 ≤ Real.exp ((cGeo * mu) * (d X : ℝ)) :=
      Real.one_le_exp_iff.mpr
        (mul_nonneg hgeom (Nat.cast_nonneg _))
    change lam * ‖z X‖ ≤ ‖(lam : ℂ) * z X‖ *
      Real.exp ((cGeo * mu) * (d X : ℝ))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0]
    exact (by
      calc
        lam * ‖z X‖ = (lam * ‖z X‖) * 1 := by ring
        _ ≤ (lam * ‖z X‖) *
            Real.exp ((cGeo * mu) * (d X : ℝ)) :=
          mul_le_mul_of_nonneg_left he
            (mul_nonneg hlam0 (norm_nonneg _)))
  have hfirst (X : Γ) (hX : X ∈ A) :
      (1 : ℝ) + w Q ≤ H (h + 1) (Sum.inl X) := by
    have hqContact :
        X ∈ actualContactRoot rootQ
          (fourDimPeriodicNeighborhood N chi) support :=
      (Finset.mem_inter.mp hX).2
    have hQchild :
        Q ∈ actualPeriodicPolymerChildren N chi supp (Sum.inl X) :=
      (actual_augmented_second_root_bulk_contact_iff
        N chi support rootQ X).mpr hqContact
    have hchildNonneg (Y : Sum Γ Unit) :
        0 ≤ w Y * H h Y :=
      mul_nonneg (hw Y) (by linarith [hFone h Y])
    have hqLow : w Q ≤ w Q * H h Q := by
      calc
        w Q = w Q * 1 := by ring
        _ ≤ w Q * H h Q :=
          mul_le_mul_of_nonneg_left (hFone h Q) (hw Q)
    have hsumLow :
        w Q ≤ ∑ Y ∈ actualPeriodicPolymerChildren N chi supp (Sum.inl X),
          w Y * H h Y := by
      exact hqLow.trans
        (Finset.single_le_sum
          (fun Y hY => hchildNonneg Y) hQchild)
    change 1 + w Q ≤
      Real.exp (∑ Y ∈ actualPeriodicPolymerChildren N chi supp (Sum.inl X),
        w Y * H h Y)
    linarith [Real.add_one_le_exp
      (∑ Y ∈ actualPeriodicPolymerChildren N chi supp (Sum.inl X),
        w Y * H h Y)]
  have hBridgeInRoot : A.image Sum.inl ⊆ R := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
    have hpContact :
        X ∈ actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi) support :=
      (Finset.mem_inter.mp hX).1
    have hp := (Finset.mem_filter.mp
      (show X ∈ (Finset.univ : Finset Γ).filter
        (fun X => ∃ Delta ∈ actualRootNeighbourhood rootP
          (fourDimPeriodicNeighborhood N chi), Delta ∈ support X)
        from hpContact)).2
    change (Sum.inl X : Sum Γ Unit) ∈
      (Finset.univ : Finset (Sum Γ Unit)).filter
        (fun Y => ∃ Delta ∈ actualRootNeighbourhood rootP
          (fourDimPeriodicNeighborhood N chi), Delta ∈ supp Y)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [supp, actualSecondRootAugmentedSupport] using hp⟩
  have hsource (X : Γ) :
      lam * eps * ‖z X‖ ≤ w (Sum.inl X) * w Q := by
    calc
      lam * eps * ‖z X‖ = (lam * ‖z X‖) * eps := by ring
      _ ≤ (lam * ‖z X‖) * w Q :=
        mul_le_mul_of_nonneg_left hqWeight
          (mul_nonneg hlam0 (norm_nonneg _))
      _ ≤ w (Sum.inl X) * w Q :=
        mul_le_mul_of_nonneg_right (hbulkWeight X) (hw Q)
  have hsumBridge :
      (∑ X ∈ A, lam * eps * ‖z X‖) ≤
      ∑ X ∈ A, w (Sum.inl X) * w Q :=
    Finset.sum_le_sum (fun X hX => hsource X)
  have hpositiveRoot :
      ∀ Y, 0 ≤ w Y * H (h + 1) Y :=
    fun Y => mul_nonneg (hw Y) (by linarith [hFone (h + 1) Y])
  have hsumTree :
      (∑ X ∈ A, w (Sum.inl X) * w Q) ≤
      ∑ X ∈ A, w (Sum.inl X) * H (h + 1) (Sum.inl X) := by
    apply Finset.sum_le_sum
    intro X hX
    exact mul_le_mul_of_nonneg_left
      (by linarith [hfirst X hX] :
        w Q ≤ H (h + 1) (Sum.inl X))
      (hw (Sum.inl X))
  have hsumImage :
      (∑ X ∈ A, w (Sum.inl X) * H (h + 1) (Sum.inl X)) =
      ∑ Y ∈ A.image Sum.inl, w Y * H (h + 1) Y := by
    symm
    apply Finset.sum_image
    intro X hX X' hX' heq
    exact Sum.inl.inj heq
  have hTreeRoot :
      (∑ X ∈ A, w (Sum.inl X) * w Q) ≤ F := by
    calc
      _ ≤ ∑ X ∈ A, w (Sum.inl X) * H (h + 1) (Sum.inl X) :=
        hsumTree
      _ = ∑ Y ∈ A.image Sum.inl, w Y * H (h + 1) Y := hsumImage
      _ ≤ ∑ Y ∈ R, w Y * H (h + 1) Y :=
        Finset.sum_le_sum_of_subset_of_nonneg
          hBridgeInRoot (fun Y hY hnot => hpositiveRoot Y)
      _ = F := rfl
  have hFinal : F ≤ Real.exp F - 1 := by
    linarith [Real.add_one_le_exp F]
  exact hsumBridge.trans (hTreeRoot.trans hFinal)

end YMUIC.Original24
