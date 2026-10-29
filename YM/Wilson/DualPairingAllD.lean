import YM.Wilson.SourceMix21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-!
C29 equations (304)--(306): exact canonical pairing of a primal
finite-dimensional Yang--Mills source frame and its inverse-transpose
dual.  No cumulative matrix norm, summability, or unitarity is needed
for the paired observable.  The result is valid for every finite source
dimension (not only 21).  It does not prove the physical source dictionary
or OS E0' all-orders test-function estimate.
-/

/-- Pure finite-dimensional algebra.  The dual relation
  sum_i Z_(i,k) B_(i,j) = delta_(k,j)
is exactly Z^T B = I, i.e. B=Z^{-T} when Z is invertible.
The pairing is BILINEAR (no conjugate), as appropriate for source
coordinates acting on an observable jet. -/
theorem source_primal_dual_pairing_allD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z B : ι → ι → ℂ)
    (hdual : ∀ k j : ι,
      (∑ i : ι, Z i k * B i j) = if k = j then 1 else 0)
    (v J : ι → ℂ) :
    (∑ i : ι, (∑ k : ι, Z i k * v k) *
      (∑ j : ι, B i j * J j)) =
      ∑ k : ι, v k * J k := by
  classical
  calc
    (∑ i : ι, (∑ k : ι, Z i k * v k) *
      (∑ j : ι, B i j * J j)) =
      ∑ i : ι, ∑ k : ι, ∑ j : ι,
        (Z i k * v k) * (B i j * J j) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ k : ι, ∑ j : ι, ∑ i : ι,
        (Z i k * v k) * (B i j * J j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ j : ι,
        (∑ i : ι, Z i k * B i j) * (v k * J j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ k : ι, ∑ j : ι,
        (if k = j then (1 : ℂ) else 0) * (v k * J j) := by
          simp_rw [hdual]
    _ = ∑ k : ι, v k * J k := by
          simp

/-- Concrete genuine-SU(2) Wilson plaquette pairing, with a finite
21-root coordinate transform.  Unlike the unpaired source norm estimate,
the exact canonically PAIRED observable has no RG-matrix amplification:
all coefficients of Z and B cancel algebraically.
This is a statement about the paired linear observable only. -/
theorem paired_wilson_source_uniform_without_cocycle_norm
    (Z B : RootFiber21 → RootFiber21 → ℂ)
    (hdual : ∀ k j : RootFiber21,
      (∑ i : RootFiber21, Z i k * B i j) =
        if k = j then 1 else 0)
    (J : RootFiber21 → ℂ)
    (U : RootFiber21 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ‖∑ i : RootFiber21,
       (∑ k : RootFiber21,
         Z i k * wilsonPlaquetteDirection U position f k) *
       (∑ j : RootFiber21, B i j * J j)‖ ≤
      4 * (∑ j : RootFiber21, ‖J j‖) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  rw [source_primal_dual_pairing_allD Z B hdual
    (wilsonPlaquetteDirection U position f) J]
  calc
    ‖∑ k : RootFiber21,
        wilsonPlaquetteDirection U position f k * J k‖ ≤
      ∑ k : RootFiber21,
        ‖wilsonPlaquetteDirection U position f k * J k‖ :=
          norm_sum_le _ _
    _ = ∑ k : RootFiber21,
        ‖wilsonPlaquetteDirection U position f k‖ * ‖J k‖ := by
          simp_rw [norm_mul]
    _ ≤ ∑ k : RootFiber21,
        (4 * SchwartzMap.seminorm ℂ 0 0 f) * ‖J k‖ := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right
            (wilson_plaquette_direction_pointwise U position f k)
            (norm_nonneg _)
    _ = 4 * (∑ k : RootFiber21, ‖J k‖) *
          SchwartzMap.seminorm ℂ 0 0 f := by
          rw [← Finset.mul_sum]
          ring

end YMUIC.Wilson
