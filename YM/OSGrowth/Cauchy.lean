import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Metric Set

namespace YMUIC.OSGrowth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_fderiv_le_cauchy {f : E → F} {c : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ x ∈ closedBall c R, ‖f x‖ ≤ M) :
    ‖fderiv ℂ f c‖ ≤ M / R := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM hR.le)
  intro v hv
  let g : ℂ → E := fun z => c + z • v
  have hg (z : ℂ) : HasDerivAt g v z := by
    simpa [g] using ((hasDerivAt_id z).smul_const v).const_add c
  have hmaps : MapsTo g (closedBall 0 R) (closedBall c R) := by
    intro z hz
    simpa [g, mem_closedBall, dist_eq_norm, norm_smul, hv] using hz
  have hd : DifferentiableOn ℂ (f ∘ g) (closedBall 0 R) :=
    hf.differentiableOn.comp (fun z _ => (hg z).differentiableAt.differentiableWithinAt) hmaps
  have hder : HasDerivAt (f ∘ g) ((fderiv ℂ f c) v) 0 := by
    have hfc : HasFDerivAt f (fderiv ℂ f c) (g 0) := by
      simpa [g] using (hf c (mem_closedBall_self hR.le)).differentiableAt.hasFDerivAt
    exact hfc.comp_hasDerivAt 0 (hg 0)
  rw [← hder.deriv]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (hd.diffContOnCl_ball (Subset.refl _))
  intro z hz
  exact hb _ (hmaps (sphere_subset_closedBall hz))

theorem norm_iteratedFDeriv_le_layers {f : E → F} {c : E} {R M δ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ x ∈ closedBall c R, ‖f x‖ ≤ M) (n : ℕ) :
    ∀ x, dist x c + n * δ ≤ R →
      ‖iteratedFDeriv ℂ n f x‖ ≤ M / δ ^ n := by
  induction n with
  | zero =>
    intro x hx
    simpa using hb x (by simpa using hx)
  | succ n ih =>
    intro x hx
    have hsub : closedBall x δ ⊆ closedBall c R := by
      intro y hy
      have := dist_triangle y x c
      have h0 : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      simp only [mem_closedBall] at hy ⊢
      push_cast at hx
      nlinarith
    have hbound : ∀ y ∈ closedBall x δ, ‖iteratedFDeriv ℂ n f y‖ ≤ M / δ ^ n := by
      intro y hy
      apply ih y
      have := dist_triangle y x c
      simp only [mem_closedBall] at hy
      push_cast at hx
      nlinarith
    calc
      ‖iteratedFDeriv ℂ (n + 1) f x‖ = ‖fderiv ℂ (iteratedFDeriv ℂ n f) x‖ :=
        norm_fderiv_iteratedFDeriv.symm
      _ ≤ (M / δ ^ n) / δ :=
        norm_fderiv_le_cauchy hδ (by positivity) ((hf.iteratedFDeriv n).mono hsub) hbound
      _ = M / δ ^ (n + 1) := by rw [div_div, pow_succ]

theorem norm_iteratedFDeriv_le_cauchy {f : E → F} {c : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ x ∈ closedBall c R, ‖f x‖ ≤ M) {n : ℕ} (hn : 0 < n) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ ((n : ℝ) / R) ^ n * M := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := norm_iteratedFDeriv_le_layers (div_pos hR hn') hM hf hb n c
    (by simp [mul_div_cancel₀ _ hn'.ne'])
  convert h using 1
  simp only [div_pow, div_div_eq_mul_div]
  ring

theorem pow_order_le_exp_mul_factorial (n : ℕ) :
    (n : ℝ) ^ n ≤ Real.exp 1 ^ n * n.factorial := by
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
  have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul 1 n
  rw [hexp] at h
  exact (div_le_iff₀ hfac).mp h

theorem cauchy_to_factorial {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (n : ℕ) :
    ((n : ℝ) / R) ^ n * M ≤ n.factorial * (Real.exp 1 / R) ^ n * M := by
  apply mul_le_mul_of_nonneg_right _ hM
  rw [div_pow, div_pow, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (pow_pos hR n)).mpr
  simpa [mul_comm] using pow_order_le_exp_mul_factorial n

theorem norm_iteratedFDeriv_le_cauchy_open {f : E → F} {c : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball c R))
    (hb : ∀ x ∈ ball c R, ‖f x‖ ≤ M) {n : ℕ} (hn : 0 < n) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ ((n : ℝ) / R) ^ n * M := by
  apply ContinuousWithinAt.closure_le (s := Ioo 0 R)
    (by rw [closure_Ioo hR.ne]; exact ⟨hR.le, le_rfl⟩)
    continuousWithinAt_const
    (((continuousAt_const.div continuousAt_id hR.ne').pow n).mul
      continuousAt_const).continuousWithinAt
  intro r hr
  exact norm_iteratedFDeriv_le_cauchy hr.1 hM
    (hf.mono (closedBall_subset_ball hr.2))
    (fun x hx => hb x (closedBall_subset_ball hr.2 hx)) hn

theorem original29_polymer_cauchy {Epoly : E → ℂ} {ρ ε κ τ : ℝ}
    (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hanalytic : AnalyticOnNhd ℂ Epoly (ball 0 ρ))
    (hweight : ∀ J ∈ ball 0 ρ, ‖Epoly J‖ ≤ ε * Real.exp (-κ * τ))
    {r : ℕ} (hr : 0 < r) (h : Fin r → E) (hh : ∀ j, ‖h j‖ ≤ 1) :
    ‖iteratedFDeriv ℂ r Epoly 0 h‖ ≤ ((r : ℝ) / ρ) ^ r *
      (ε * Real.exp (-κ * τ)) := by
  have hd := norm_iteratedFDeriv_le_cauchy_open hρ
    (mul_nonneg hε (Real.exp_pos _).le) hanalytic hweight hr
  simpa using ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le hd hh

theorem original29_polymer_factorial {Epoly : E → ℂ} {ρ ε κ τ : ℝ}
    (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hanalytic : AnalyticOnNhd ℂ Epoly (ball 0 ρ))
    (hweight : ∀ J ∈ ball 0 ρ, ‖Epoly J‖ ≤ ε * Real.exp (-κ * τ))
    {r : ℕ} (hr : 0 < r) (h : Fin r → E) (hh : ∀ j, ‖h j‖ ≤ 1) :
    ‖iteratedFDeriv ℂ r Epoly 0 h‖ ≤ r.factorial * (Real.exp 1 / ρ) ^ r *
      (ε * Real.exp (-κ * τ)) :=
  (original29_polymer_cauchy hρ hε hanalytic hweight hr h hh).trans
    (cauchy_to_factorial hρ (mul_nonneg hε (Real.exp_pos _).le) r)

end YMUIC.OSGrowth
