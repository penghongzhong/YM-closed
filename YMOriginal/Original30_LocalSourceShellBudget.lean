import YMOriginal.Original30_LocalSourcePolymerMoments
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30

/-!
Original 30's geometric-series budget, for the active source polymers.
The support and length of the physical RG polymers, source-locality and
the shell-count hypothesis still have to be derived from the actual model.
-/

theorem active_polymer_shell_budget
    {ι : Type*} (F : Finset ι) (length : ι → ℕ)
    (ε C κ σ : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hgap : σ < κ)
    (hcount : ∀ m : ℕ,
      ((F.filter (fun i => length i = m)).card : ℝ) ≤
        C * Real.exp (σ * (m : ℝ))) :
    (∑ i ∈ F, ε * Real.exp (-κ * (length i : ℝ))) ≤
      ε * C / (1 - Real.exp (-(κ - σ))) := by
  classical
  let q : ℝ := Real.exp (-(κ - σ))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hGeom : Summable (fun m : ℕ => q ^ m) :=
    summable_geometric_of_lt_one hq0 hq1
  have hGeomSum : (∑' m : ℕ, q ^ m) = (1 - q)⁻¹ :=
    tsum_geometric_of_lt_one hq0 hq1
  let w : ℕ → ℝ := fun m => Real.exp (-κ * (m : ℝ))
  have hFiber : (∑ i ∈ F, w (length i)) =
      ∑ m ∈ F.image length, ∑ i ∈ F with length i = m, w m := by
    symm
    apply Finset.sum_fiberwise_of_maps_to'
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hShell (m : ℕ) :
      (∑ i ∈ F with length i = m, w m) ≤ C * q ^ m := by
    have hId : Real.exp (σ * (m : ℝ)) * w m = q ^ m := by
      dsimp [w, q]
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    calc
      (∑ i ∈ F with length i = m, w m) =
          ((F.filter (fun i => length i = m)).card : ℝ) * w m := by
            simp [nsmul_eq_mul]
      _ ≤ (C * Real.exp (σ * (m : ℝ))) * w m :=
        mul_le_mul_of_nonneg_right (hcount m) (Real.exp_pos _).le
      _ = C * q ^ m := by rw [mul_assoc, hId]
  have hsum : (∑ i ∈ F, w (length i)) ≤ C * (1-q)⁻¹ := by
    calc
      _ = ∑ m ∈ F.image length, ∑ i ∈ F with length i = m, w m := hFiber
      _ ≤ ∑ m ∈ F.image length, C * q ^ m :=
        Finset.sum_le_sum (fun m hm => hShell m)
      _ = C * (∑ m ∈ F.image length, q ^ m) := by rw [Finset.mul_sum]
      _ ≤ C * (∑' m : ℕ, q ^ m) :=
        mul_le_mul_of_nonneg_left
          (hGeom.sum_le_tsum (F.image length) (fun m hm => pow_nonneg hq0 _)) hC
      _ = C * (1-q)⁻¹ := by rw [hGeomSum]
  calc
    (∑ i ∈ F, ε * Real.exp (-κ * (length i : ℝ))) =
        ε * (∑ i ∈ F, w (length i)) := by rw [Finset.mul_sum]
    _ ≤ ε * (C * (1-q)⁻¹) := mul_le_mul_of_nonneg_left hsum hε
    _ = ε * C / (1 - Real.exp (-(κ - σ))) := by
      dsimp [q]
      rw [div_eq_mul_inv]
      ring

theorem local_source_moments_from_shell_count
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : Finset ι) (active : ι → Prop) [DecidablePred active]
    (activity : ι → E → ℂ) (length : ι → ℕ)
    (ε C κ σ ρ : ℝ) (hρ : 0 < ρ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hgap : σ < κ)
    (hlocal : ∀ i ∈ Γ, ¬ active i → ∀ J ∈ Metric.ball 0 ρ,
      activity i J = activity i 0)
    (hanalytic : ∀ i ∈ Γ.filter active,
      AnalyticOnNhd ℂ (activity i) (Metric.ball 0 ρ))
    (hweight : ∀ i ∈ Γ.filter active, ∀ J ∈ Metric.ball 0 ρ,
      ‖activity i J‖ ≤ ε * Real.exp (-κ * (length i : ℝ)))
    (hcount : ∀ m : ℕ,
      (((Γ.filter active).filter (fun i => length i = m)).card : ℝ) ≤
        C * Real.exp (σ * (m : ℝ))) :
    let A := ε * C / (1 - Real.exp (-(κ - σ)))
    let Z : E → ℂ := fun J =>
      Complex.exp ((∑ i ∈ Γ, activity i J) - ∑ i ∈ Γ, activity i 0)
    AnalyticOnNhd ℂ Z (Metric.ball 0 ρ) ∧ Z 0 = 1 ∧
      ∀ (r : ℕ) (h : Fin r → E),
        ‖iteratedFDeriv ℂ r Z 0 h‖ ≤
          Real.exp 1 * (r.factorial : ℝ) *
            (Real.exp 1 * (1 + 2 * A) / ρ) ^ r * ∏ j, ‖h j‖ := by
  have hden : 0 < 1 - Real.exp (-(κ - σ)) := by
    have he : Real.exp (-(κ - σ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hA : 0 ≤ ε * C / (1 - Real.exp (-(κ - σ))) :=
    div_nonneg (mul_nonneg hε hC) hden.le
  exact local_polymer_source_normalized_moments Γ active activity
    (fun i => ε * Real.exp (-κ * (length i : ℝ))) hρ hA hlocal
      hanalytic hweight (active_polymer_shell_budget
        (Γ.filter active) length ε C κ σ hε hC hgap hcount)

#print axioms active_polymer_shell_budget
#print axioms local_source_moments_from_shell_count

end YMUIC.Original30
