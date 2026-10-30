import YMOriginal.Original24_PeriodicFourDimContact
import YMOriginal.Original24_TwoRootFullRadius

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# One-connected-polymer two-root estimate from ACTUAL U1 block activity

This is a genuine single-history analogue of original24 (317):
* two actual SU2 Wilson word source roots at p,q (full radius),
* a polymer touching both real root supports on the periodic N^4 torus,
* SAME finite polynomial support/length d(X) throughout,
* the actual per-block UNMARKED source norm, NOT a pre-assumed root tree sum.

The bridge is an explicitly defined intersection of two finite root
contact families; the root distance must be bounded by the native
polymer length for this one-polymer connected case. Multi-polymer
Ursell/Penrose/FP connected trees require the separate U2 proof,
so do not promote Original24 based on this special subcase alone.
-/

/-- A true one-polymer bridge touches both source root neighborhoods
in the same physical periodic N^4 lattice. -/
def actualOnePolymerTwoRootBridge
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) : Finset Γ :=
  actualContactRoot rootP (fourDimPeriodicNeighborhood N chi) support ∩
    actualContactRoot rootQ (fourDimPeriodicNeighborhood N chi) support

/-- The actual two-root SOURCE-NORM bound for one connected polymer,
derived using only the genuine unmarked per-block U1 activity norm
and the true periodic lattice coordination count, not any hU2 tree sum
or a source-deformed R-operation hypothesis. -/
theorem actual_one_polymer_two_root_from_local_U1
    {P T S Γ : Type*} [Fintype T] [Fintype S] [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (z : Γ → ℂ) (length : Γ → ℝ)
    (kappa mu cGeo cRt dRoot aAct : ℝ)
    (hmu : 0 ≤ mu)
    (hlength : ∀ X, 0 ≤ length X)
    (hkappa : mu * cGeo ≤ kappa)
    (haAct : 0 ≤ aAct)
    (hgeom : ∀ X ∈ actualOnePolymerTwoRootBridge
      N chi rootP rootQ support,
      dRoot ≤ cRt + cGeo * length X)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * length X)) ≤ aAct) :
    (∑ X ∈ actualOnePolymerTwoRootBridge
      N chi rootP rootQ support,
      ‖actualTwoRootMarkedR U wp cp wq cq s t z X‖) ≤
      ((Real.exp (radius * Bp) - 1) *
        (Real.exp (radius * Bq) - 1)) *
      Real.exp (mu * cRt) *
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (rootP.card : ℝ) * aAct *
      Real.exp (-mu * dRoot) := by
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  have hkp : 0 ≤ Real.exp (radius * Bp) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hr hp0)
    linarith
  have hkq : 0 ≤ Real.exp (radius * Bq) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hr hq0)
    linarith
  have hK : 0 ≤ K := mul_nonneg hkp hkq
  have hD : ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤ K :=
    actual_two_root_insertion_full_radius
      U wp cp wq cq s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  let weight : Γ → ℝ := fun X =>
    ‖z X‖ * Real.exp (kappa * length X)
  have hweight : ∀ X, 0 ≤ weight X := by
    intro X
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hRootNorm :
      (∑ X ∈ actualContactRoot rootP
        (fourDimPeriodicNeighborhood N chi) support, weight X) ≤
      ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (rootP.card : ℝ)) * aAct :=
    periodic_four_dim_root_contact_from_U1_norm
      N chi rootP support weight aAct hweight haAct hLocalNorm
  let bridge := actualOnePolymerTwoRootBridge N chi rootP rootQ support
  have hsubset :
      bridge ⊆ actualContactRoot rootP
        (fourDimPeriodicNeighborhood N chi) support :=
    Finset.inter_subset_left
  have hBridgeNorm :
      (∑ X ∈ bridge, weight X) ≤
      ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (rootP.card : ℝ)) * aAct := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun X _ _ => hweight X)).trans hRootNorm
  have hPoint (X : Γ) (hX : X ∈ bridge) :
      Real.exp (mu * dRoot) *
        ‖actualTwoRootMarkedR U wp cp wq cq s t z X‖ ≤
          K * Real.exp (mu * cRt) * weight X := by
    have hg := hgeom X hX
    have hµ : mu * dRoot ≤
        mu * cRt + kappa * length X := by
      have hmul :=
        mul_le_mul_of_nonneg_left hg hmu
      have hlen := hlength X
      nlinarith [mul_le_mul_of_nonneg_right hkappa hlen]
    have hexp :
        Real.exp (mu * dRoot) ≤
          Real.exp (mu * cRt) * Real.exp (kappa * length X) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hµ
    calc
      Real.exp (mu * dRoot) *
          ‖actualTwoRootMarkedR U wp cp wq cq s t z X‖ =
        ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
          (Real.exp (mu * dRoot) * ‖z X‖) := by
            simp only [actualTwoRootMarkedR, norm_mul]
            ring
      _ ≤ ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
          ((Real.exp (mu * cRt) * Real.exp (kappa * length X)) *
            ‖z X‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ ≤ K * ((Real.exp (mu * cRt) *
          Real.exp (kappa * length X)) * ‖z X‖) := by
            apply mul_le_mul_of_nonneg_right hD
            positivity
      _ = K * Real.exp (mu * cRt) * weight X := by
        dsimp [weight]
        ring
  have hKexp : 0 ≤ K * Real.exp (mu * cRt) := by positivity
  have hWeighted :
      (∑ X ∈ bridge, Real.exp (mu * dRoot) *
        ‖actualTwoRootMarkedR U wp cp wq cq s t z X‖) ≤
      (K * Real.exp (mu * cRt)) *
        ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (rootP.card : ℝ) * aAct) := by
    calc
      _ ≤ ∑ X ∈ bridge,
          (K * Real.exp (mu * cRt)) * weight X := by
            apply Finset.sum_le_sum
            intro X hX
            exact hPoint X hX
      _ = (K * Real.exp (mu * cRt)) *
          (∑ X ∈ bridge, weight X) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hBridgeNorm hKexp
  have hCancel :
      Real.exp (-mu * dRoot) * Real.exp (mu * dRoot) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    (∑ X ∈ bridge,
        ‖actualTwoRootMarkedR U wp cp wq cq s t z X‖) =
      Real.exp (-mu * dRoot) *
        (∑ X ∈ bridge,
          Real.exp (mu * dRoot) *
            ‖actualTwoRootMarkedR U wp cp wq cq s t z X‖) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro X _
              rw [← mul_assoc, hCancel, one_mul]
    _ ≤ Real.exp (-mu * dRoot) *
        ((K * Real.exp (mu * cRt)) *
          ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
          (rootP.card : ℝ) * aAct)) :=
          mul_le_mul_of_nonneg_left hWeighted (Real.exp_pos _).le
    _ = ((Real.exp (radius * Bp) - 1) *
          (Real.exp (radius * Bq) - 1)) *
        Real.exp (mu * cRt) *
        (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (rootP.card : ℝ) * aAct *
        Real.exp (-mu * dRoot) := by dsimp [K]; ring

end YMUIC.Original24
