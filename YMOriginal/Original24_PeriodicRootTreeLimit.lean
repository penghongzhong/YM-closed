import YMOriginal.Original24_PeriodicKPFiniteTree
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original24

/-!
# Full infinite-height periodic U2 rooted-tree recursion

The genuine periodic N^4 finite-polymer KP recursion has a monotone,
bounded infinite-height limit WITHOUT assuming convergence or a
rooted-tree-sum upper bound. The only non-internal data are the
unmarked per-block U1 analytic activity norm and explicit KP
smallness. The labeled Ursell/Penrose/Fernandez-Procacci tree
IDENTIFICATION with the physical Yang-Mills cumulant remains open.
-/

/-- The actual rooted-tree finite-height first attachment sum
over finite periodic block supports, using the SAME U1 activity z
and U2 finite-height recursive child weights at every h. -/
def actualPeriodicFirstRootSum
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu : ℝ) (h : ℕ) : ℝ :=
  ∑ X ∈ actualContactRoot root
      (fourDimPeriodicNeighborhood N chi) support,
    (‖z X‖ * Real.exp ((cGeo * mu) * (d X : ℝ))) *
      actualPeriodicTreeHeight N chi support
        (fun Y => ‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ))) h X

/-- Positivity alone makes every finite-height KP child tree
monotonically increase in height. No tree-enumeration result used. -/
theorem actual_periodic_tree_height_mono
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (weight : Γ → ℝ) (hw : ∀ Y, 0 ≤ weight Y) :
    ∀ h X, actualPeriodicTreeHeight N chi support weight h X ≤
      actualPeriodicTreeHeight N chi support weight (h + 1) X := by
  intro h
  induction h with
  | zero =>
      intro X
      change (1 : ℝ) ≤ Real.exp
        (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
          weight Y * 1)
      apply Real.one_le_exp_iff.mpr
      apply Finset.sum_nonneg
      intro Y _
      exact mul_nonneg (hw Y) (by norm_num)
  | succ h ih =>
      intro X
      change Real.exp
        (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
          weight Y * actualPeriodicTreeHeight N chi support weight h Y) ≤
        Real.exp
          (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
            weight Y * actualPeriodicTreeHeight N chi support weight (h + 1) Y)
      apply Real.exp_le_exp.mpr
      apply Finset.sum_le_sum
      intro Y _
      exact mul_le_mul_of_nonneg_left (ih Y) (hw Y)

/-- Original per-block U1 activity and the physical 4D chi-neighborhood
derive a UNIFORM finite-height first-root tree bound. -/
theorem actual_periodic_first_root_uniform
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct) :
    ∀ h,
      actualPeriodicFirstRootSum N chi root support z d cGeo mu h ≤
        ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct := by
  have hKP := actual_periodic_U2_tree_height_bound
    N chi support z d kappa mu cGeo aAct
    ha hdelta hsize hsmall hLocalNorm
  let baseWeight : Γ → ℝ := fun X =>
    ‖z X‖ * Real.exp (kappa * (d X : ℝ))
  have hbasePos : ∀ X, 0 ≤ baseWeight X := by
    intro X
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hRoot := periodic_four_dim_root_contact_from_U1_norm
      N chi root support baseWeight aAct hbasePos ha hLocalNorm
  have hfrac :
      cGeo * mu + (kappa - cGeo * mu) / 2 ≤ kappa := by
    linarith [hdelta]
  intro h
  calc
    actualPeriodicFirstRootSum N chi root support z d cGeo mu h ≤
      (∑ X ∈ actualContactRoot root
        (fourDimPeriodicNeighborhood N chi) support,
          baseWeight X) := by
          unfold actualPeriodicFirstRootSum
          apply Finset.sum_le_sum
          intro X _
          have hX := hKP h X
          have hw : 0 ≤
              ‖z X‖ * Real.exp ((cGeo * mu) * (d X : ℝ)) := by
            positivity
          have hs :
              Real.exp ((cGeo * mu) * (d X : ℝ)) *
                Real.exp (((kappa - cGeo * mu) / 2) * (d X : ℝ)) ≤
              Real.exp (kappa * (d X : ℝ)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_right hfrac
              (Nat.cast_nonneg (d X))]
          calc
            _ ≤
              (‖z X‖ * Real.exp ((cGeo * mu) * (d X : ℝ))) *
                Real.exp (((kappa - cGeo * mu) / 2) * (d X : ℝ)) :=
              mul_le_mul_of_nonneg_left hX hw
            _ = ‖z X‖ *
              (Real.exp ((cGeo * mu) * (d X : ℝ)) *
                Real.exp (((kappa - cGeo * mu) / 2) * (d X : ℝ))) :=
              by ring
            _ ≤ ‖z X‖ * Real.exp (kappa * (d X : ℝ)) :=
              mul_le_mul_of_nonneg_left hs (norm_nonneg _)
            _ = baseWeight X := rfl
    _ ≤ ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct := hRoot

/-- The original U1 data actually produce an INFINITE-HEIGHT rooted KP
limit, bounded uniformly in the regulator, without assuming tree
convergence or an abstract upper bound on the completed tree. The
physical connected Ursell sum must still be IDENTIFIED with this
KP recursive tree limit through the published FP theorem. -/
theorem actual_periodic_first_root_limit_exists_and_bounded
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct) :
    ∃ fullRootTree : ℝ,
      Tendsto (actualPeriodicFirstRootSum N chi root support z d cGeo mu)
        atTop (nhds fullRootTree) ∧
      fullRootTree ≤
        ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct := by
  let F : ℕ → ℝ :=
    actualPeriodicFirstRootSum N chi root support z d cGeo mu
  have hMono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro h
    unfold F actualPeriodicFirstRootSum
    apply Finset.sum_le_sum
    intro X _
    exact mul_le_mul_of_nonneg_left
      (actual_periodic_tree_height_mono N chi support
        (fun Y => ‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ)))
        (fun Y => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) h X)
      (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hBound := actual_periodic_first_root_uniform N chi root
    support z d kappa mu cGeo aAct ha hdelta hsize hsmall hLocalNorm
  have hBdd : BddAbove (Set.range F) := by
    refine ⟨((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (root.card : ℝ)) * aAct, ?_⟩
    rintro y ⟨h, rfl⟩
    exact hBound h
  let fullRootTree : ℝ := ⨆ h, F h
  have hlim : Tendsto F atTop (nhds fullRootTree) :=
    tendsto_atTop_ciSup hMono hBdd
  refine ⟨fullRootTree, hlim, ?_⟩
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall hBound

end YMUIC.Original24
