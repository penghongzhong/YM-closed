import Mathlib

set_option autoImplicit false

/-!
# U2 root does not enter bulk placement entropy: final rootbound assembly

Standalone final assembly corresponding to v133 `lem:root`.

Inputs already certified in preceding nodes:
* pointwise Penrose + two bounded external roots;
* root-distance exponential extraction;
* rooted-tree majorant with total <= Nroot * aAct.

The weighted pointwise estimate is represented explicitly as
  exp(mu*dRoot) * phi(Gamma)
    <= Kr^2 * exp(mu*cRt) * treeWeight(Gamma).

The theorem removes the common exponential weight and performs the nonnegative
tsum comparison, yielding exactly
  Croot * aAct * exp(-mu*dRoot),
with
  Croot = Kr^2 * exp(mu*cRt) * Nroot.
-/

namespace YMUICV128.Section03.T007D

noncomputable def Croot
    (Kr mu cRt : ℝ) (Nroot : ℕ) : ℝ :=
  Kr ^ 2 * Real.exp (mu * cRt) * (Nroot : ℝ)

theorem unweight_pointwise
    {Cluster : Type*}
    (phi treeWeight : Cluster → ℝ)
    (Kr mu cRt dRoot : ℝ)
    (hphi : ∀ Γ, 0 ≤ phi Γ)
    (htree : ∀ Γ, 0 ≤ treeWeight Γ)
    (hweighted :
      ∀ Γ,
        Real.exp (mu * dRoot) * phi Γ
          ≤
        Kr ^ 2 * Real.exp (mu * cRt) * treeWeight Γ) :
    ∀ Γ,
      phi Γ
        ≤
      (Kr ^ 2 * Real.exp (mu * cRt) *
        Real.exp (-mu * dRoot)) * treeWeight Γ := by
  intro Γ
  have hneg : 0 ≤ Real.exp (-mu * dRoot) :=
    (Real.exp_pos _).le
  have h :=
    mul_le_mul_of_nonneg_left (hweighted Γ) hneg
  have hcancel :
      Real.exp (-mu * dRoot) * Real.exp (mu * dRoot) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    phi Γ
        = (Real.exp (-mu * dRoot) *
            Real.exp (mu * dRoot)) * phi Γ := by
          rw [hcancel, one_mul]
    _ =
      Real.exp (-mu * dRoot) *
        (Real.exp (mu * dRoot) * phi Γ) := by
      ring
    _ ≤
      Real.exp (-mu * dRoot) *
        (Kr ^ 2 * Real.exp (mu * cRt) * treeWeight Γ) :=
      h
    _ =
      (Kr ^ 2 * Real.exp (mu * cRt) *
        Real.exp (-mu * dRoot)) * treeWeight Γ := by
      ring

theorem rootbound_from_tree_majorant
    {Cluster : Type*}
    (phi treeWeight : Cluster → ℝ)
    (Kr mu cRt aAct : ℝ)
    (dRoot : ℝ)
    (Nroot : ℕ)
    (hphi : ∀ Γ, 0 ≤ phi Γ)
    (htree : ∀ Γ, 0 ≤ treeWeight Γ)
    (hKr : 0 ≤ Kr)
    (haAct : 0 ≤ aAct)
    (hweighted :
      ∀ Γ,
        Real.exp (mu * dRoot) * phi Γ
          ≤
        Kr ^ 2 * Real.exp (mu * cRt) * treeWeight Γ)
    (hsumTree : Summable treeWeight)
    (htreeTotal :
      (∑' Γ, treeWeight Γ)
        ≤ (Nroot : ℝ) * aAct) :
    (∑' Γ, phi Γ)
      ≤
    Croot Kr mu cRt Nroot *
      aAct * Real.exp (-mu * dRoot) := by
  let C :
      ℝ :=
    Kr ^ 2 * Real.exp (mu * cRt) *
      Real.exp (-mu * dRoot)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint :
      ∀ Γ, phi Γ ≤ C * treeWeight Γ := by
    intro Γ
    dsimp [C]
    exact unweight_pointwise
      phi treeWeight Kr mu cRt dRoot
      hphi htree hweighted Γ
  have hCMajor :
      Summable (fun Γ => C * treeWeight Γ) :=
    hsumTree.mul_left C
  have hPhiSum :
      Summable phi :=
    Summable.of_nonneg_of_le hphi hpoint hCMajor
  have hsum1 :
      (∑' Γ, phi Γ)
        ≤ ∑' Γ, C * treeWeight Γ :=
    hPhiSum.tsum_le_tsum hpoint hCMajor
  have hsum2 :
      (∑' Γ, C * treeWeight Γ)
        ≤ C * ((Nroot : ℝ) * aAct) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htreeTotal hC
  calc
    (∑' Γ, phi Γ)
        ≤ C * ((Nroot : ℝ) * aAct) :=
      hsum1.trans hsum2
    _ =
      Croot Kr mu cRt Nroot *
        aAct * Real.exp (-mu * dRoot) := by
      dsimp [C, Croot]
      ring

#print axioms unweight_pointwise
#print axioms rootbound_from_tree_majorant

end YMUICV128.Section03.T007D
