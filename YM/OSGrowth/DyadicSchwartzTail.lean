import YM.OSGrowth.DyadicCutoffDerivativeBound

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.OSGrowth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [FiniteDimensional ℝ E]

/-- The actual dyadic cutoff applied to a Schwartz test, as a Schwartz map. -/
def dyadicSchwartzCutoff (n : ℕ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  ((dyadicCutoff (E := E) n).hasCompactSupport.smul_right
    (f' := (f : E → ℂ))).toSchwartzMap
      ((dyadicCutoff (E := E) n).contDiff.smul (f.smooth ⊤))

/-- An explicit, cutoff-index-independent budget for the tail in p_(k,m). -/
def dyadicSchwartzTailBudget (k m : ℕ) (f : SchwartzMap E ℂ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ 0 i (baseCutoffSchwartz (E := E)) + 1) *
      SchwartzMap.seminorm ℂ (k + 1) (m - i) f

/-- Every Schwartz seminorm of the actual cutoff error decays at least as
2^(-n). Only one additional spatial weight is used; no approximation or
density hypothesis is supplied. -/
theorem dyadic_schwartz_tail_bound (n k m : ℕ) (f : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℂ k m (dyadicSchwartzCutoff n f - f) ≤
      dyadicSchwartzTailBudget k m f / (2 : ℝ) ^ n := by
  let a : E → ℝ := fun x => dyadicCutoff (E := E) n x - 1
  have ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a :=
    (dyadicCutoff (E := E) n).contDiff.sub contDiff_const
  have heq : ((dyadicSchwartzCutoff n f - f : SchwartzMap E ℂ) : E → ℂ) =
      fun x => a x • f x := by
    funext x
    change dyadicCutoff (E := E) n x • f x - f x = _
    simp only [a, sub_smul, one_smul]
  have hM (i : ℕ) : 0 ≤ SchwartzMap.seminorm ℝ 0 i
      (baseCutoffSchwartz (E := E)) := apply_nonneg _ _
  have hA (i : ℕ) (x : E) : ‖iteratedFDeriv ℝ i a x‖ ≤
      SchwartzMap.seminorm ℝ 0 i (baseCutoffSchwartz (E := E)) + 1 := by
    have hcut := dyadic_cutoff_derivative_bound (E := E) n i x
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (n * i) := one_le_pow₀ (by norm_num)
    have hcut' : ‖iteratedFDeriv ℝ i (dyadicCutoff (E := E) n) x‖ ≤
        SchwartzMap.seminorm ℝ 0 i (baseCutoffSchwartz (E := E)) :=
      hcut.trans (div_le_self (hM i) hp)
    have hconst : ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) x‖ ≤ 1 := by
      cases i with
      | zero => simp
      | succ i => simp [iteratedFDeriv_succ_const]
    have hd : iteratedFDeriv ℝ i a x =
        iteratedFDeriv ℝ i (dyadicCutoff (E := E) n) x -
          iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) x :=
      iteratedFDeriv_sub_apply
        (dyadicCutoff (E := E) n).contDiff.contDiffAt contDiffAt_const
    rw [hd]
    exact (norm_sub_le _ _).trans (add_le_add hcut' hconst)
  have hB : 0 ≤ dyadicSchwartzTailBudget k m f := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [hM i]))
      (apply_nonneg _ _)
  apply SchwartzMap.seminorm_le_bound ℂ k m _ (div_nonneg hB (by positivity))
  intro x
  rw [heq]
  by_cases hx : ‖x‖ < (2 : ℝ) ^ n
  · have hone := (dyadicCutoff (E := E) n).eventuallyEq_one_of_mem_ball
      (by simpa [Metric.mem_ball, dist_zero_right, dyadicCutoff] using hx)
    have hz : (fun y => a y • f y) =ᶠ[𝓝 x] (fun _ : E => (0 : ℂ)) := by
      filter_upwards [hone] with y hy
      simp only [a, hy, Pi.one_apply, sub_self, zero_smul]
    have hd := (hz.iteratedFDeriv ℝ m).eq_of_nhds
    rw [hd]
    simpa using div_nonneg hB (by positivity : (0 : ℝ) ≤ 2 ^ n)
  · have hx' : (2 : ℝ) ^ n ≤ ‖x‖ := le_of_not_gt hx
    have htail (j : ℕ) : ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ ≤
        SchwartzMap.seminorm ℂ (k + 1) j f / (2 : ℝ) ^ n := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      calc
        _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_left hx' (by positivity)
        _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j f x‖ := by rw [pow_succ]; ring
        _ ≤ SchwartzMap.seminorm ℂ (k + 1) j f := f.le_seminorm ℂ _ _ _
    calc
      _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
            ‖iteratedFDeriv ℝ (m - i) f x‖ :=
        mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_smul_le ha (f.smooth ⊤) x (by simp)) (by positivity)
      _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i a x‖ * (‖x‖ ^ k *
            ‖iteratedFDeriv ℝ (m - i) f x‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          (SchwartzMap.seminorm ℝ 0 i (baseCutoffSchwartz (E := E)) + 1) *
            (SchwartzMap.seminorm ℂ (k + 1) (m - i) f / (2 : ℝ) ^ n) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hA i x) (Nat.cast_nonneg _))
          (htail (m - i)) (by positivity)
          (mul_nonneg (Nat.cast_nonneg _) (by linarith [hM i]))
      _ = dyadicSchwartzTailBudget k m f / (2 : ℝ) ^ n := by
        simp only [dyadicSchwartzTailBudget, Finset.sum_div, mul_div_assoc]

end YMUIC.OSGrowth
