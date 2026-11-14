import YMOriginal.Original24_FromPublishedU1ConnectedFP
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUICV128.Section02

/-!
# C29 / B11 actual U1 native polymer shell count -> block activity norm

The v133 original manuscript Section U1 already states the physical
uniform shell geometry:
  #{X containing Delta : m <= d_j(X) < m+1}
       <= C_pol * exp(c_pol*m).
This file uses that precise UNMARKED geometry and the real
Balaban old-R/new-R pointwise bounds to DERIVE the weighted
per-block history norm used by the exact n+2 Mayer/FP theorem.

There is NO separate hypothesis hcount for the completed block sum.
For native integer-length d, m <= d < m+1 is exactly d=m.
All constants are independent of cutoff/volume PROVIDED the
actual native U1 physical shell bound is uniform.

The Yang--Mills CMP119/CMP122 original history-to-integer
polymer-length/support dictionary remains an analytic model
obligation and cannot be assumed proved by this arithmetic lemma.
-/

/-- The exact finite-shell geometric summation from native
polymer length and exponential shell count; no total hcount input.

The summation formula uses Finset.sum_fiberwise_of_maps_to'
so each actual polymer is counted exactly once. -/
theorem actual_native_U1_shell_count_to_block_norm
    {Γ Block : Type*} [Fintype Γ] [DecidableEq Block]
    (support : Γ → Finset Block) (d : Γ → ℕ)
    (Cpol cpol kappaR kappa : ℝ)
    (hCpol : 0 ≤ Cpol)
    (hgap : 0 < kappaR - kappa - cpol)
    (hShell : ∀ Delta : Block, ∀ m : ℕ,
      ((actualThroughBlock support Delta).filter
        (fun X => d X = m)).card ≤
        Cpol * Real.exp (cpol * (m : ℝ))) :
    ∀ Delta : Block,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(kappaR - kappa) * (d X : ℝ))) ≤
      Cpol / (1 - Real.exp (-(kappaR - kappa - cpol))) := by
  classical
  let gap : ℝ := kappaR - kappa - cpol
  let q : ℝ := Real.exp (-gap)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q, gap]
    exact Real.exp_lt_one_iff.mpr (by linarith [hgap])
  have hGeom : Summable (fun m : ℕ => q ^ m) :=
    summable_geometric_of_lt_one hq0 hq1
  have hGeomSum :
      (∑' m : ℕ, q ^ m) = (1 - q)⁻¹ :=
    tsum_geometric_of_lt_one hq0 hq1
  intro Delta
  let F : Finset Γ := actualThroughBlock support Delta
  let weight : ℕ → ℝ := fun m =>
    Real.exp (-(kappaR - kappa) * (m : ℝ))
  have hFiber :
      (∑ X ∈ F, weight (d X)) =
      ∑ m ∈ F.image d,
        ∑ X ∈ F with d X = m, weight m := by
    symm
    apply Finset.sum_fiberwise_of_maps_to'
    intro X hX
    exact Finset.mem_image.mpr ⟨X, hX, rfl⟩
  have hShellSum (m : ℕ) :
      (∑ X ∈ F with d X = m, weight m) ≤
        Cpol * q ^ m := by
    have hcount : ((F.filter (fun X => d X = m)).card : ℝ) ≤
        Cpol * Real.exp (cpol * (m : ℝ)) := hShell Delta m
    have hId :
        Real.exp (cpol * (m : ℝ)) * weight m = q ^ m := by
      dsimp [weight, q, gap]
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    calc
      (∑ X ∈ F with d X = m, weight m) =
          ((F.filter (fun X => d X = m)).card : ℝ) *
            weight m := by
            simp [nsmul_eq_mul]
      _ ≤ (Cpol * Real.exp (cpol * (m : ℝ))) * weight m :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
      _ = Cpol * q ^ m := by
        rw [mul_assoc, hId]
  have hSum :
      (∑ X ∈ F, weight (d X)) ≤ Cpol * (1 - q)⁻¹ := by
    calc
      (∑ X ∈ F, weight (d X)) =
        ∑ m ∈ F.image d,
          ∑ X ∈ F with d X = m, weight m := hFiber
      _ ≤ ∑ m ∈ F.image d, Cpol * q ^ m :=
        Finset.sum_le_sum (fun m hm => hShellSum m)
      _ = Cpol * (∑ m ∈ F.image d, q ^ m) := by
        rw [Finset.mul_sum]
      _ ≤ Cpol * (∑' m : ℕ, q ^ m) := by
        exact mul_le_mul_of_nonneg_left
          (hGeom.sum_le_tsum (F.image d)
            (fun m hm => pow_nonneg hq0 _)) hCpol
      _ = Cpol * (1 - q)⁻¹ := by
        rw [hGeomSum]
  change (∑ X ∈ F, weight (d X)) ≤
    Cpol / (1 - Real.exp (-gap))
  simpa only [q, div_eq_mul_inv] using hSum

end YMUIC.Original24
