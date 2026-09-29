import Mathlib

set_option autoImplicit false

/-!
# U2 root majorant: nonnegative infinite-sum comparison

Generic M-test / comparison step used in v133 equation `rootstep4`.

If a nonnegative cluster summand phi is pointwise bounded by
  C * treeWeight,
and treeWeight is summable with total <= M, then
  tsum phi <= C*M.

This isolates the infinite cluster-sum step from the geometric and Penrose
pointwise estimates.
-/

namespace YMUICV128.Section03.T007C

theorem nonnegative_tsum_comparison
    {Cluster : Type*}
    (phi treeWeight : Cluster → ℝ)
    (C M : ℝ)
    (hphi : ∀ Γ, 0 ≤ phi Γ)
    (htree : ∀ Γ, 0 ≤ treeWeight Γ)
    (hC : 0 ≤ C)
    (hpoint : ∀ Γ, phi Γ ≤ C * treeWeight Γ)
    (hsumTree : Summable treeWeight)
    (htreeTotal : (∑' Γ, treeWeight Γ) ≤ M) :
    Summable phi ∧ (∑' Γ, phi Γ) ≤ C * M := by
  have hCMajor :
      Summable (fun Γ => C * treeWeight Γ) :=
    hsumTree.mul_left C
  have hPhiSum :
      Summable phi :=
    Summable.of_nonneg_of_le hphi hpoint hCMajor
  have hTsum :
      (∑' Γ, phi Γ)
        ≤ ∑' Γ, C * treeWeight Γ :=
    hPhiSum.tsum_le_tsum hpoint hCMajor
  have hMajorTotal :
      (∑' Γ, C * treeWeight Γ) ≤ C * M := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htreeTotal hC
  exact ⟨hPhiSum, hTsum.trans hMajorTotal⟩

#print axioms nonnegative_tsum_comparison

end YMUICV128.Section03.T007C
