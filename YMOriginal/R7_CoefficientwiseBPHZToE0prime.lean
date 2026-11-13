import YMOriginal.Original34_OSII_ExternalInterface
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
noncomputable section

namespace YMUIC.R7
open YMUIC.Original34

/-- Coefficientwise BPHZ shell data: the actual hierarchy is the exact
sum of renormalized RG-age shells, and each shell has the R7 geometric
fifth-order surplus on the full joint Schwartz test space.

The certificate does NOT assume E0'; it exposes the model-facing
obligations shell-by-shell. -/
structure CoefficientwiseBPHZShellCertificate
    (H : SchwingerHierarchy) where
  decay : ℝ
  decay_nonneg : 0 ≤ decay
  decay_lt_one : decay < 1
  q : ℕ
  k : ℕ
  A : ℝ
  C : ℝ
  A_nonneg : 0 ≤ A
  C_pos : 0 < C
  shell : (r m : ℕ) → JointTest r →L[ℂ] ℂ
  shell_bound :
    ∀ (r m : ℕ) (f : JointTest r),
      ‖shell r m f‖ ≤
        ((A * C ^ r * (Nat.factorial r : ℝ)) *
          YMUIC.OSTensor.jointSchwartzControl r q (k * r) f) *
          decay ^ m
  telescope :
    ∀ (r : ℕ) (f : JointTest r),
      H.S r f = ∑' m : ℕ, shell r m f

/-- Exact geometric RG-age summation turns the coefficientwise BPHZ
shell estimate into the corrected joint OS E0' bound.

All convergence is derived here; no pre-existing E0' or summability of
the completed hierarchy is a premise. -/
theorem coefficientwise_bphz_shells_imply_E0prime
    (H : SchwingerHierarchy)
    (B : CoefficientwiseBPHZShellCertificate H) :
    OS_E0prime H := by
  have hden : 0 < 1 - B.decay := sub_pos.mpr B.decay_lt_one
  refine ⟨B.q, B.k, B.A / (1 - B.decay), B.C,
    div_nonneg B.A_nonneg hden.le, B.C_pos, ?_⟩
  intro r f
  let P : ℝ :=
    YMUIC.OSTensor.jointSchwartzControl r B.q (B.k * r) f
  let K : ℝ := (B.A * B.C ^ r * (Nat.factorial r : ℝ)) * P
  have hP : 0 ≤ P := apply_nonneg _ _
  have hCpow : 0 ≤ B.C ^ r := pow_nonneg B.C_pos.le r
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgeom : Summable (fun m : ℕ => B.decay ^ m) :=
    summable_geometric_of_lt_one B.decay_nonneg B.decay_lt_one
  have hmajor : Summable (fun m : ℕ => K * B.decay ^ m) :=
    hgeom.mul_left K
  have hsNorm : Summable (fun m : ℕ => ‖B.shell r m f‖) := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hmajor
    simpa only [K, P] using B.shell_bound r m f
  have hs : Summable (fun m : ℕ => B.shell r m f) :=
    summable_norm_iff.mp hsNorm
  rw [B.telescope r f]
  calc
    ‖∑' m : ℕ, B.shell r m f‖ ≤
        ∑' m : ℕ, ‖B.shell r m f‖ :=
      norm_tsum_le_tsum_norm hsNorm
    _ ≤ ∑' m : ℕ, K * B.decay ^ m :=
      hsNorm.tsum_le_tsum
        (fun m => by simpa only [K, P] using B.shell_bound r m f)
        hmajor
    _ = K * (1 - B.decay)⁻¹ := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one B.decay_nonneg B.decay_lt_one]
    _ = ((B.A / (1 - B.decay)) * B.C ^ r *
          (Nat.factorial r : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r B.q (B.k * r) f := by
      dsimp [K, P]
      rw [div_eq_mul_inv]
      ring

#print axioms coefficientwise_bphz_shells_imply_E0prime

end YMUIC.R7
