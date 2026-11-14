import YMOriginal.Original24_PeriodicFourDimContact

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# U2 finite-height KP trees on true periodic 4D polymer supports

The children of each polymer are EXACTLY those touching its finite
periodic chi-neighborhood. The KP child barrier is derived from the
original per-block U1 activity norm and true 4D neighbor cardinality,
rather than introduced as the output-sized hypothesis.
No full infinite connected-tree/FP identification is asserted here.
-/

def actualPeriodicPolymerChildren
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (X : Γ) : Finset Γ :=
  actualContactRoot (support X)
    (fourDimPeriodicNeighborhood N chi) support

def actualPeriodicTreeHeight
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (weight : Γ → ℝ) : ℕ → Γ → ℝ
  | 0, _ => 1
  | n + 1, X =>
      Real.exp (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
        weight Y * actualPeriodicTreeHeight N chi support weight n Y)

/-- The precise U2 KP child inequality, not assumed, follows from
the unmarked U1 norm over each physical block. -/
theorem actual_periodic_U1_to_U2_child_barrier
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
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
    ∀ X,
      (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
        (‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ))) *
          Real.exp (((kappa - cGeo * mu) / 2) * (d Y : ℝ))) ≤
        ((kappa - cGeo * mu) / 2) * (d X : ℝ) := by
  intro X
  let delta : ℝ := kappa - cGeo * mu
  let baseWeight : Γ → ℝ := fun Y =>
    ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))
  have hBasePos : ∀ Y, 0 ≤ baseWeight Y := by
    intro Y
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hRoot :=
    periodic_four_dim_root_contact_from_U1_norm
      N chi (support X) support baseWeight aAct
      hBasePos ha hLocalNorm
  have hfrac : cGeo * mu + delta / 2 ≤ kappa := by
    dsimp [delta]
    linarith
  have hterm (Y : Γ) :
      (‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ))) *
        Real.exp ((delta / 2) * (d Y : ℝ)) ≤ baseWeight Y := by
    have he : Real.exp ((cGeo * mu) * (d Y : ℝ)) *
      Real.exp ((delta / 2) * (d Y : ℝ)) ≤
      Real.exp (kappa * (d Y : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hfrac
        (Nat.cast_nonneg (d Y))]
    calc
      (‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ))) *
        Real.exp ((delta / 2) * (d Y : ℝ)) =
        ‖z Y‖ *
          (Real.exp ((cGeo * mu) * (d Y : ℝ)) *
            Real.exp ((delta / 2) * (d Y : ℝ))) := by ring
      _ ≤ ‖z Y‖ * Real.exp (kappa * (d Y : ℝ)) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = baseWeight Y := rfl
  have hcardX : ((support X).card : ℝ) ≤ (d X : ℝ) :=
    Nat.cast_le.mpr (hsize X)
  have hdelta0 : 0 ≤ delta / 2 := by dsimp [delta]; linarith [hdelta]
  calc
    (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
      (‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ))) *
        Real.exp ((delta / 2) * (d Y : ℝ))) ≤
      ∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
        baseWeight Y := by
        apply Finset.sum_le_sum
        intro Y _
        exact hterm Y
    _ ≤ (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (↑(support X).card : ℝ) * aAct := hRoot
    _ = ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct) *
      (↑(support X).card : ℝ) := by ring
    _ ≤ (delta / 2) * (↑(support X).card : ℝ) :=
      mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)
    _ ≤ (delta / 2) * (d X : ℝ) :=
      mul_le_mul_of_nonneg_left hcardX hdelta0

/-- Uniform over ALL finite tree heights, with no asserted tree bound
among the theorem hypotheses. -/
theorem actual_periodic_U2_tree_height_bound
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
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
    ∀ h X,
      actualPeriodicTreeHeight N chi support
        (fun Y => ‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ)))
        h X ≤
      Real.exp (((kappa - cGeo * mu) / 2) * (d X : ℝ)) := by
  let weight : Γ → ℝ := fun Y =>
    ‖z Y‖ * Real.exp ((cGeo * mu) * (d Y : ℝ))
  let barrier : Γ → ℝ := fun Y =>
    ((kappa - cGeo * mu) / 2) * (d Y : ℝ)
  have hw : ∀ Y, 0 ≤ weight Y := by
    intro Y
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hBarrier : ∀ Y, 0 ≤ barrier Y := by
    intro Y
    dsimp [barrier]
    exact mul_nonneg (by linarith [hdelta]) (Nat.cast_nonneg _)
  have hChild (X : Γ) :
      (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
        weight Y * Real.exp (barrier Y)) ≤ barrier X :=
    actual_periodic_U1_to_U2_child_barrier
      N chi support z d kappa mu cGeo aAct
      ha hdelta hsize hsmall hLocalNorm X
  intro h
  induction h with
  | zero =>
      intro X
      change (1 : ℝ) ≤ Real.exp (barrier X)
      exact Real.one_le_exp_iff.mpr (hBarrier X)
  | succ h ih =>
      intro X
      change Real.exp
        (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
          weight Y * actualPeriodicTreeHeight
            N chi support weight h Y) ≤ Real.exp (barrier X)
      apply Real.exp_le_exp.mpr
      calc
        (∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
          weight Y * actualPeriodicTreeHeight N chi support weight h Y) ≤
          ∑ Y ∈ actualPeriodicPolymerChildren N chi support X,
            weight Y * Real.exp (barrier Y) := by
            apply Finset.sum_le_sum
            intro Y _
            exact mul_le_mul_of_nonneg_left (ih Y) (hw Y)
        _ ≤ barrier X := hChild X

end YMUIC.Original24
