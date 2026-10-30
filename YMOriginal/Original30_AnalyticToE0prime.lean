import YMOriginal.Original34_OSII_ExternalInterface
import YM.OSGrowth.Cauchy

set_option autoImplicit false
noncomputable section
open Metric Filter

namespace YMUIC.Original30

/-!
# Original30: a noncircular sufficient producer for corrected OS E0'

Crucial distinction: this lemma obtains the FULL joint 4r-variable
Schwartz E0' factorial growth (not only factorized pure tensors)
from a uniformly bounded analytic generating map with values in
continuous joint-test distributions. The analytic source map and its
coefficient dictionary are still ACTUAL Yang--Mills RG model
obligations; neither is assumed automatically from the bounded Wilson
bare root or source-mixing matrix invertibility.

The same q,k and radius rho hold for ALL r and joint tests.
No growth bound on S_r is assumed for r >= 1, and no pre-existing
E0' estimate appears as a premise.
-/

/-- Scalar analytic source chart for all joint 4r-variable test functions,
with a uniform-in-r complex disk and a uniform seminorm majorant.
The r-th source derivative is exactly the r-point Schwinger distribution,
which is a genuine source/field dictionary that must be checked for YM. -/
structure JointSourceAnalyticCertificate
    (H : YMUIC.Original34.SchwingerHierarchy) where
  radius : ℝ
  radius_pos : 0 < radius
  q k : ℕ
  M : ℝ
  M_ge_one : 1 ≤ M
  source : (r : ℕ) → YMUIC.Original34.JointTest r → ℂ → ℂ
  analytic : ∀ (r : ℕ) (f : YMUIC.Original34.JointTest r),
    AnalyticOnNhd ℂ (source r f) (ball 0 radius)
  majorant : ∀ (r : ℕ) (f : YMUIC.Original34.JointTest r)
      (s : ℂ), s ∈ ball 0 radius →
    ‖source r f s‖ ≤
      M * YMUIC.OSTensor.jointSchwartzControl r q (k * r) f
  coefficient : ∀ (r : ℕ) (f : YMUIC.Original34.JointTest r),
    H.S r f = (iteratedFDeriv ℂ r (source r f) 0)
      (fun _ : Fin r => (1 : ℂ))
  normalizes : ∀ f : YMUIC.Original34.JointTest 0,
    H.S 0 f = f 0

/-- A single joint analytic source radius, if derived from the ACTUAL
physical RG/Schwinger generating map, implies the full corrected OS E0'
all-order factorial distribution bound. The analytic radius is not a
conclusion of the present proof. -/
theorem joint_source_analytic_implies_os_E0prime
    (H : YMUIC.Original34.SchwingerHierarchy)
    (C : JointSourceAnalyticCertificate H) :
    YMUIC.Original34.OS_E0prime H := by
  refine ⟨C.q, C.k, C.M, Real.exp 1 / C.radius,
    (by linarith [C.M_ge_one]), (div_pos (Real.exp_pos _) C.radius_pos), ?_⟩
  intro r f
  by_cases hr : r = 0
  · subst r
    have hnorm : ‖H.S 0 f‖ ≤
        YMUIC.OSTensor.jointSchwartzControl 0 C.q (C.k * 0) f := by
      rw [C.normalizes f]
      have hpoint : ‖f (0 : EuclideanSpace ℝ (Fin 0))‖ ≤
          SchwartzMap.seminorm ℂ 0 0 f :=
        f.norm_le_seminorm ℂ (0 : EuclideanSpace ℝ (Fin 0))
      exact hpoint.trans
        ((YMUIC.OSTensor.joint_schwartz_control 0 C.q (C.k * 0)).2
          f 0 (by omega)).1
    have hp : 0 ≤ YMUIC.OSTensor.jointSchwartzControl
        0 C.q (C.k * 0) f := apply_nonneg _ _
    have hM : YMUIC.OSTensor.jointSchwartzControl
        0 C.q (C.k * 0) f ≤
      C.M * YMUIC.OSTensor.jointSchwartzControl
        0 C.q (C.k * 0) f := by
      calc
        _ = 1 * YMUIC.OSTensor.jointSchwartzControl
            0 C.q (C.k * 0) f := by ring
        _ ≤ C.M * YMUIC.OSTensor.jointSchwartzControl
            0 C.q (C.k * 0) f :=
            mul_le_mul_of_nonneg_right C.M_ge_one hp
    simpa using hnorm.trans hM
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let P : ℝ := YMUIC.OSTensor.jointSchwartzControl
      r C.q (C.k * r) f
    have hp : 0 ≤ P := apply_nonneg _ _
    have hM : 0 ≤ C.M * P := mul_nonneg (by linarith [C.M_ge_one]) hp
    have hCauchy :=
      YMUIC.OSGrowth.norm_iteratedFDeriv_le_cauchy_open
        (f := C.source r f) (c := (0 : ℂ))
        (R := C.radius) (M := C.M * P)
        C.radius_pos hM (C.analytic r f)
        (by
          intro s hs
          exact C.majorant r f s hs)
        hrpos
    have hone : ∀ (j : Fin r), ‖(1 : ℂ)‖ ≤ (1 : ℝ) := by
      intro j
      norm_num
    have hpoint :
        ‖(iteratedFDeriv ℂ r (C.source r f) 0)
          (fun _ : Fin r => (1 : ℂ))‖ ≤
          (((r : ℝ) / C.radius) ^ r) * (C.M * P) := by
      simpa using ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
        hCauchy hone
    have hfac := YMUIC.OSGrowth.cauchy_to_factorial
      C.radius_pos hM r
    calc
      ‖H.S r f‖ =
          ‖(iteratedFDeriv ℂ r (C.source r f) 0)
            (fun _ : Fin r => (1 : ℂ))‖ := by rw [C.coefficient r f]
      _ ≤ (((r : ℝ) / C.radius) ^ r) * (C.M * P) := hpoint
      _ ≤ (r.factorial : ℝ) * (Real.exp 1 / C.radius) ^ r *
        (C.M * P) := hfac
      _ = (C.M * (Real.exp 1 / C.radius) ^ r *
        (r.factorial : ℝ)) *
        YMUIC.OSTensor.jointSchwartzControl r C.q (C.k * r) f := by
        dsimp [P]
        ring

#print axioms joint_source_analytic_implies_os_E0prime

end YMUIC.Original30
