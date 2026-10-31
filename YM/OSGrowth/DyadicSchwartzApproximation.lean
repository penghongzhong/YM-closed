import YM.OSGrowth.DyadicSchwartzTail

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.OSGrowth

/-- The concrete dyadic cutoffs are compactly supported and converge in
the full Schwartz topology, at every spatial weight and derivative order. -/
theorem dyadic_schwartz_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ) :
    (∀ n, HasCompactSupport (dyadicSchwartzCutoff n f : E → ℂ)) ∧
    Tendsto (fun n => dyadicSchwartzCutoff n f) atTop (𝓝 f) := by
  constructor
  · intro n
    exact (dyadicCutoff (E := E) n).hasCompactSupport.smul_right
  · apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ _).mpr
    rintro ⟨k, m⟩ ε hε
    have ht : Tendsto (fun n : ℕ =>
        dyadicSchwartzTailBudget k m f / (2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul
            (dyadicSchwartzTailBudget k m f)
    filter_upwards [ht.eventually_lt_const hε] with n hn
    exact (dyadic_schwartz_tail_bound n k m f).trans_lt hn

end YMUIC.OSGrowth
