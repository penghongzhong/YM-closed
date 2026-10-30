import YMOriginal.Original24_TwoRootOldNewU1
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Filter.AtTopBot.Field

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

open Filter Topology

/-!
# Original24: genuine U1 small coupling closes BOTH old/new FP budgets

The published-type estimates control real old-R activity by
  C_R * g^kappa0
and new-R activity by
  C_R_new * exp(-p0(g)).
They are uniformly small on a COMMON (0,gStop] whenever
kappa0>0 and p0(g)->+infinity as g->0+.

Neither the FP smallness conclusion nor marked-R analyticity
is taken as a theorem input. This is a mathematical reduction
of the actual old/new terminal hsmall inputs to standard
quantified weak-coupling asymptotics. It does not establish
these asymptotic hypotheses for the real CMP119/122 physical
R histories: that is a separate model-level obligation.
-/

/-- The ACTUAL two published U1 old/new R prefactors vanish together
at weak coupling under their precise analytic exponent assumptions. -/
theorem original24_old_new_U1_factors_tendsto_zero
    (kappa0 CR CRnew : ℝ) (p0 : ℝ → ℝ)
    (hkappa : 0 < kappa0)
    (hp0 : Tendsto p0 (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun g : ℝ => oldRActivityFactor g kappa0 CR)
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun g : ℝ => newRActivityFactor g CRnew p0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun g : ℝ => g)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun g : ℝ => g ^ kappa0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hid.rpow_const_nhds_zero hkappa
  have hn : Tendsto (fun g : ℝ => -p0 g)
      (𝓝[>] (0 : ℝ)) atBot := by
    have h := (tendsto_const_mul_atBot_of_neg
      (f := p0) (r := (-1 : ℝ)) (l := 𝓝[>] (0 : ℝ))
      (by norm_num)).mpr hp0
    simpa only [neg_one_mul] using h
  have he : Tendsto (fun g : ℝ => Real.exp (-p0 g))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hn
  constructor
  · simpa only [oldRActivityFactor] using hp.const_mul CR
  · simpa only [newRActivityFactor] using he.const_mul CRnew

/-- One common physical weak-coupling stopping bound makes
BOTH actual FP smallness hypotheses true, for the SAME
geometric activity weight and the SAME running g.

No artificial hsmallOld/hsmallNew assumptions appear. -/
theorem original24_old_new_FP_margin_from_decay
    (kappa0 CR CRnew Ccount B delta gMax : ℝ)
    (p0 : ℝ → ℝ)
    (hkappa : 0 < kappa0)
    (hp0 : Tendsto p0 (𝓝[>] (0 : ℝ)) atTop)
    (hdelta : 0 < delta) (hgMax : 0 < gMax) :
    ∃ gStop : ℝ, 0 < gStop ∧ gStop ≤ gMax ∧
      ∀ g : ℝ, 0 < g → g ≤ gStop →
        8 * B * (oldRActivityFactor g kappa0 CR * Ccount) ≤ delta ∧
        8 * B * (newRActivityFactor g CRnew p0 * Ccount) ≤ delta := by
  obtain ⟨hOld, hNew⟩ :=
    original24_old_new_U1_factors_tendsto_zero
      kappa0 CR CRnew p0 hkappa hp0
  have hOld0 : Tendsto
      (fun g : ℝ =>
        8 * B * (oldRActivityFactor g kappa0 CR * Ccount))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((hOld.mul_const Ccount).const_mul (8 * B))
    exact h
  have hNew0 : Tendsto
      (fun g : ℝ =>
        8 * B * (newRActivityFactor g CRnew p0 * Ccount))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((hNew.mul_const Ccount).const_mul (8 * B))
    exact h
  have hev : {g : ℝ |
      8 * B * (oldRActivityFactor g kappa0 CR * Ccount) < delta ∧
      8 * B * (newRActivityFactor g CRnew p0 * Ccount) < delta}
      ∈ (𝓝[>] (0 : ℝ)) :=
    (hOld0.eventually (Iio_mem_nhds hdelta)).and
      (hNew0.eventually (Iio_mem_nhds hdelta))
  obtain ⟨gBound, hgBound, hSubset⟩ :=
    (mem_nhdsGT_iff_exists_Ioc_subset).mp hev
  refine ⟨min gBound gMax, lt_min hgBound hgMax,
    min_le_right _ _, ?_⟩
  intro g hg hgle
  have hIn : g ∈ Set.Ioc (0 : ℝ) gBound :=
    ⟨hg, hgle.trans (min_le_left _ _)⟩
  exact ⟨le_of_lt (hSubset hIn).1, le_of_lt (hSubset hIn).2⟩

end YMUIC.Original24
