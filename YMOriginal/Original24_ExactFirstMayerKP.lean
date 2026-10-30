import YMOriginal.Original24_ExactFirstUrsell
import YMOriginal.Original24_FPFirstConnectedBulk

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original24 n=1: full actual Mayer coefficient → actual KP FP bound

The first nonzero n=1 term of the original n+2-vertex, two-Wilson
root, signed Mayer-Ursell series is computed exactly:
  M_1(z) = sum_{X touching BOTH p and q} z(X).

This is not an assumed root coefficient nor an arbitrary tree weight.
It follows from the exact three-vertex star graph signed graph sum
and the canonical 1/1! source symmetry factor.

The previously certified genuine augmented q-KP recursion then gives
  lambda*epsilon*||M_1(z)|| <= exp(F_{h+1})-1
for all finite heights and the physically correct cGeo*mu>=0.
Neither the universal all-n FP theorem nor the Penrose theorem is
a premise. The all-n Mayer/FP estimate remains open.
-/

/-- Exact first nonzero connected Mayer coefficient in the original
two-root n+2 hard-core graph, including all actual physical
bulk labels and no artificial root-root edge. -/
theorem original24_exact_first_mayer_eq_bridge_sum
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    actualExactTwoRootMayerTerm 1 N chi rootP rootQ support z =
      ∑ X ∈ actualOnePolymerTwoRootBridge N chi rootP rootQ support,
        z X := by
  classical
  let bridge := actualOnePolymerTwoRootBridge N chi rootP rootQ support
  let fterm : (Fin 1 → Γ) → ℂ := fun tuple =>
    if (actualExactTwoRootGraph 1 N chi
        rootP rootQ support tuple).Connected then
      (actualExactTwoRootUrsellCoefficient 1 N chi
        rootP rootQ support tuple : ℂ) *
        ∏ i : Fin 1, z (tuple i)
    else 0
  let gterm : Γ → ℂ := fun X =>
    if X ∈ bridge then z X else 0
  have hpoint (tuple : Fin 1 → Γ) :
      fterm tuple = gterm (tuple 0) := by
    by_cases hb : tuple 0 ∈ bridge
    · have hc :
          (actualExactTwoRootGraph 1 N chi
            rootP rootQ support tuple).Connected :=
        (original24_exact_one_bulk_graph_connected_iff
          N chi rootP rootQ support tuple).mpr hb
      have hcoeff :=
        original24_exact_one_bulk_ursell_eq_bridge_indicator
          N chi rootP rootQ support tuple
      have hcoefone :
          actualExactTwoRootUrsellCoefficient 1 N chi
            rootP rootQ support tuple = 1 := by
        simpa only [bridge, hb, ite_true] using hcoeff
      simp [fterm, gterm, hc, hb, hcoefone, Fin.prod_univ_one]
    · have hc :
          ¬(actualExactTwoRootGraph 1 N chi
            rootP rootQ support tuple).Connected := by
        intro hconn
        exact hb
          ((original24_exact_one_bulk_graph_connected_iff
            N chi rootP rootQ support tuple).mp hconn)
      simp [fterm, gterm, hc, hb]
  let e : (Fin 1 → Γ) ≃ Γ :=
    { toFun := fun tuple => tuple 0
      invFun := fun X _ => X
      left_inv := by
        intro tuple
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := by
        intro X
        rfl }
  have hsum :
      (∑ tuple : Fin 1 → Γ, fterm tuple) =
        ∑ X : Γ, gterm X :=
    Fintype.sum_equiv e fterm gterm (by
      intro tuple
      change fterm tuple = gterm (tuple 0)
      exact hpoint tuple)
  have hbridge :
      (∑ X : Γ, gterm X) =
        ∑ X ∈ bridge, z X := by
    simp [gterm, Finset.sum_filter]
  change (Nat.factorial 1 : ℂ)⁻¹ *
      (∑ tuple : Fin 1 → Γ, fterm tuple) =
      ∑ X ∈ bridge, z X
  simpa using hsum.trans hbridge

/-- The n=1 physical Mayer coefficient satisfies the TRUE KP
two-fugacity inequality without hFP, Penrose, or a prescribed
Ursell majorant; this is a complete exact-order theorem. -/
theorem original24_exact_first_mayer_from_KP
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (cGeo mu lam eps : ℝ)
    (hgeom : 0 ≤ cGeo * mu)
    (hlam : 1 ≤ lam) (heps : 0 < eps)
    (h : ℕ) :
    lam * eps *
        ‖actualExactTwoRootMayerTerm 1
          N chi rootP rootQ support z‖ ≤
      Real.exp
        (actualPeriodicFirstRootSum N chi rootP
          (actualSecondRootAugmentedSupport N support rootQ)
          (actualSecondRootAugmentedActivity
            (fun X => (lam : ℂ) * z X) eps)
          (actualSecondRootAugmentedSize d rootQ.card)
          cGeo mu (h + 1)) - 1 := by
  let bridge := actualOnePolymerTwoRootBridge
    N chi rootP rootQ support
  have hn :
      ‖actualExactTwoRootMayerTerm 1 N chi rootP rootQ support z‖ ≤
        ∑ X ∈ bridge, ‖z X‖ := by
    rw [original24_exact_first_mayer_eq_bridge_sum]
    exact norm_sum_le _ _
  have hfactor : 0 ≤ lam * eps :=
    mul_nonneg (by linarith [hlam]) heps.le
  calc
    lam * eps *
      ‖actualExactTwoRootMayerTerm 1 N chi rootP rootQ support z‖ ≤
        lam * eps * (∑ X ∈ bridge, ‖z X‖) :=
      mul_le_mul_of_nonneg_left hn hfactor
    _ = ∑ X ∈ bridge, lam * eps * ‖z X‖ := by rw [Finset.mul_sum]
    _ ≤ Real.exp
      (actualPeriodicFirstRootSum N chi rootP
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSecondRootAugmentedActivity
          (fun X => (lam : ℂ) * z X) eps)
        (actualSecondRootAugmentedSize d rootQ.card)
        cGeo mu (h + 1)) - 1 :=
      original24_FP_one_bulk_connected_from_KP
        N chi rootP rootQ support z d cGeo mu
        lam eps hgeom hlam heps h

end YMUIC.Original24
