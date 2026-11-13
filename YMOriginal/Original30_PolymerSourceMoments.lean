import YM.OSGrowth.Cauchy
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

open Metric Set

namespace YMUIC.Original30

/-!
# Finite polymer log sources give normalized full moments

The generating function in the conclusion is constructed from the supplied
polymer activities, including subtraction of its value at zero. No moment
bound, cumulant bound, coefficient identity, or source-radius certificate for
the exponentiated function is assumed.

The prefactor is independent of the activity budget A; the dependence on A
is polynomial of degree r. In particular this avoids the exp(A) support
dependence obtained by estimating the partition sum on a fixed source ball.

This is the analytic log-source-to-moment step for Original 30. Constructing
these activities for the actual renormalized Yang--Mills source, obtaining
regulator-uniform input budgets, and extending to arbitrary joint Schwartz
tests are separate obligations. This theorem does not close Original 30.
-/

/-- A bounded analytic finite polymer log source has factorially bounded
normalized full moments, for every order including zero and arbitrary source
directions. All dependence on a support/activity budget is polynomial in A.
The same constants apply to every finite polymer set satisfying the inputs. -/
theorem polymer_source_normalized_moments
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : Finset ι) (activity : ι → E → ℂ) (weight : ι → ℝ)
    {ρ A : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hanalytic : ∀ i ∈ Γ, AnalyticOnNhd ℂ (activity i) (ball 0 ρ))
    (hweight : ∀ i ∈ Γ, ∀ J ∈ ball 0 ρ, ‖activity i J‖ ≤ weight i)
    (hbudget : ∑ i ∈ Γ, weight i ≤ A) :
    let Z : E → ℂ := fun J =>
      Complex.exp ((∑ i ∈ Γ, activity i J) - ∑ i ∈ Γ, activity i 0)
    AnalyticOnNhd ℂ Z (ball 0 ρ) ∧ Z 0 = 1 ∧
      ∀ (r : ℕ) (h : Fin r → E),
        ‖iteratedFDeriv ℂ r Z 0 h‖ ≤
          Real.exp 1 * (r.factorial : ℝ) *
            (Real.exp 1 * (1 + 2 * A) / ρ) ^ r * ∏ j, ‖h j‖ := by
  let H : E → ℂ := fun J => ∑ i ∈ Γ, activity i J
  let Z : E → ℂ := fun J => Complex.exp (H J - H 0)
  change AnalyticOnNhd ℂ Z (ball 0 ρ) ∧ Z 0 = 1 ∧ _
  have hH : AnalyticOnNhd ℂ H (ball 0 ρ) := by
    have heq : H = ∑ i ∈ Γ, activity i := by
      funext J
      simp [H]
    rw [heq]
    exact Finset.analyticOnNhd_sum Γ (fun i hi => hanalytic i hi)
  have hbound (J : E) (hJ : J ∈ ball 0 ρ) : ‖H J‖ ≤ A := by
    exact (norm_sum_le Γ _).trans
      ((Finset.sum_le_sum (fun i hi => hweight i hi J hJ)).trans hbudget)
  have hZ : AnalyticOnNhd ℂ Z (ball 0 ρ) :=
    (hH.sub analyticOnNhd_const).cexp
  refine ⟨hZ, by simp [Z], ?_⟩
  intro r h
  have hden : 0 < 1 + 2 * A := by positivity
  let R : ℝ := ρ / (1 + 2 * A)
  have hR : 0 < R := div_pos hρ hden
  have hRρ : R ≤ ρ := by
    dsimp [R]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have hmaps : MapsTo H (ball 0 ρ) (closedBall (H 0) (2 * A)) := by
    intro J hJ
    simp only [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      linarith [hbound J hJ, hbound 0 (mem_ball_self hρ)])
  have hsmall (J : E) (hJ : J ∈ ball 0 R) : ‖Z J‖ ≤ Real.exp 1 := by
    have hJρ : J ∈ ball 0 ρ := ball_subset_ball hRρ hJ
    have hschwarz : ‖H J - H 0‖ ≤ (2 * A / ρ) * ‖J‖ := by
      simpa [dist_eq_norm] using
        Complex.dist_le_div_mul_dist_of_mapsTo_ball hH.differentiableOn hmaps hJρ
    have hnorm : ‖J‖ ≤ R := by
      exact (mem_ball_zero_iff.mp hJ).le
    have hcenter : ‖H J - H 0‖ ≤ 1 := by
      calc
        _ ≤ (2 * A / ρ) * ‖J‖ := hschwarz
        _ ≤ (2 * A / ρ) * R :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = 2 * A / (1 + 2 * A) := by dsimp [R]; field_simp
        _ ≤ 1 := (div_le_one hden).mpr (by linarith)
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hcenter)
  have hop : ‖iteratedFDeriv ℂ r Z 0‖ ≤
      Real.exp 1 * (r.factorial : ℝ) *
        (Real.exp 1 * (1 + 2 * A) / ρ) ^ r := by
    cases r with
    | zero =>
      simp only [norm_iteratedFDeriv_zero, Z, sub_self, Complex.exp_zero,
        norm_one, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
      exact Real.one_le_exp (by norm_num)
    | succ n =>
      have hc := YMUIC.OSGrowth.norm_iteratedFDeriv_le_cauchy_open
        hR (Real.exp_pos 1).le (hZ.mono (ball_subset_ball hRρ)) hsmall
        (Nat.succ_pos n)
      have hf := hc.trans (YMUIC.OSGrowth.cauchy_to_factorial
        hR (Real.exp_pos 1).le (n + 1))
      simpa only [R, div_div_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using hf
  exact (iteratedFDeriv ℂ r Z 0).le_opNorm h |>.trans
    (mul_le_mul_of_nonneg_right hop (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

end YMUIC.Original30
