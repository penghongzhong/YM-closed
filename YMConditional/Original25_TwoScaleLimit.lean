import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace YMUIC.RotationMatching

/-- The four-dimensional placement entropy is paid by the fifth-order surplus.
This ratio is fixed before the cutoff-volume index and the history split. -/
def historyRatio (L theta : ℝ) : ℝ := L ^ (-(1 - theta))

theorem historyRatio_bounds {L theta : ℝ} (hL : 1 < L) (htheta : theta < 1) :
    0 < historyRatio L theta ∧ historyRatio L theta < 1 := by
  have hL0 : 0 < L := lt_trans (by norm_num) hL
  exact ⟨Real.rpow_pos_of_pos hL0 _,
    Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)⟩

/-- Exact entropy/irrelevance cancellation, with no interchange of coupling
powers and cutoff powers. The exponent 4 is not suppressed in this identity. -/
theorem placement_surplus_identity {L theta : ℝ} (hL : 0 < L) (m : ℕ) :
    L ^ (4 * (m : ℝ)) * L ^ (-(5 - theta) * (m : ℝ)) =
      historyRatio L theta ^ m := by
  rw [← Real.rpow_add hL]
  have hexp : 4 * (m : ℝ) + -(5 - theta) * (m : ℝ) =
      -(1 - theta) * (m : ℝ) := by ring
  rw [hexp, Real.rpow_mul hL.le, Real.rpow_natCast]
  rfl

/-- The whole old-history tail, not a finite truncation. -/
theorem old_history_series {L theta : ℝ} (hL : 1 < L) (htheta : theta < 1)
    (N : ℕ) :
    HasSum (fun k : ℕ =>
      L ^ (4 * ((N + k : ℕ) : ℝ)) *
        L ^ (-(5 - theta) * ((N + k : ℕ) : ℝ)))
      (historyRatio L theta ^ N / (1 - historyRatio L theta)) := by
  obtain ⟨hq0, hq1⟩ := historyRatio_bounds hL htheta
  have hs := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left
    (historyRatio L theta ^ N)
  simpa only [placement_surplus_identity (lt_trans (by norm_num) hL),
    pow_add, div_eq_mul_inv] using hs

/-- Recent histories are sent to zero at each FIXED history cut. The modulus
needs only its original right-hand limit; no two-sided continuity is added. -/
theorem recent_error_tendsto {ι : Type*} {l : Filter ι}
    (a g : ι → ℝ) (epsilon : ℝ → ℝ)
    (ha : Tendsto a l (𝓝 0)) (hg : Tendsto g l (𝓝 0))
    (hgpos : ∀ᶠ i in l, 0 < g i)
    (hepsilon : Tendsto epsilon (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun i => (a i)^2 + epsilon (g i)) l (𝓝 0) := by
  have hgRight : Tendsto g l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hg, hgpos⟩
  simpa using (ha.pow 2).add (hepsilon.comp hgRight)

/-- First limit, at a fixed history cut N. No diagonal sequence N(i), no
uniform bound on the recent-history constant, and no continuum symmetry
are assumed. The two regulator families converge along the SAME filter. -/
theorem fixed_cut_limit_bound
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F G old recent : ι → ℂ} {F0 G0 : ℂ}
    {tail C : ℝ} {err : ι → ℝ}
    (hF : Tendsto F l (𝓝 F0)) (hG : Tendsto G l (𝓝 G0))
    (herr : Tendsto err l (𝓝 0))
    (hsplit : ∀ᶠ i in l, F i - G i = old i + recent i)
    (hold : ∀ᶠ i in l, ‖old i‖ ≤ tail)
    (hrecent : ∀ᶠ i in l, ‖recent i‖ ≤ C * err i) :
    ‖F0 - G0‖ ≤ tail := by
  have hbound : ∀ᶠ i in l, ‖F i - G i‖ ≤ tail + C * err i := by
    filter_upwards [hsplit, hold, hrecent] with i hi ho hr
    rw [hi]
    exact (norm_add_le _ _).trans (add_le_add ho hr)
  have hright : Tendsto (fun i => tail + C * err i) l (𝓝 tail) := by
    simpa using (herr.const_mul C).const_add tail
  exact le_of_tendsto_of_tendsto (hF.sub hG).norm hright hbound

/-- Two-stage limit in the paper's order: first remove cutoff/volume at each
fixed N, then send N to infinity. C_recent may depend arbitrarily on N. -/
theorem equal_limits_of_old_recent
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F G : ι → ℂ} {F0 G0 : ℂ} {q C : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hF : Tendsto F l (𝓝 F0)) (hG : Tendsto G l (𝓝 G0))
    (old recent : ℕ → ι → ℂ) (C_recent : ℕ → ℝ) (err : ι → ℝ)
    (herr : Tendsto err l (𝓝 0))
    (hsplit : ∀ N, ∀ᶠ i in l, F i - G i = old N i + recent N i)
    (hold : ∀ N, ∀ᶠ i in l, ‖old N i‖ ≤ C * q^N / (1-q))
    (hrecent : ∀ N, ∀ᶠ i in l, ‖recent N i‖ ≤ C_recent N * err i) :
    F0 = G0 := by
  have hN : ∀ N : ℕ, ‖F0 - G0‖ ≤ C * q^N / (1-q) := by
    intro N
    exact fixed_cut_limit_bound hF hG herr (hsplit N) (hold N) (hrecent N)
  have htail : Tendsto (fun N : ℕ => C * q^N / (1-q)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C).div_const (1-q)
  have hzero : ‖F0 - G0‖ ≤ 0 := ge_of_tendsto htail (Eventually.of_forall hN)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

end YMUIC.RotationMatching
