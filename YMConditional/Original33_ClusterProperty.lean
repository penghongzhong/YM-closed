import YMConditional.Original33_ClusterTail

set_option autoImplicit false
noncomputable section
namespace YMUIC.ConditionalCluster

open Filter
open scoped Topology BigOperators

variable {Cluster : Type*}

/-- C29 Original33, paper Lemma17.8, the full all-orders E4 transfer.
The upstream connected/cumulant partition identity is explicitly required,
not a clustering or decay hypothesis. The actual physical distance dictionary
uses the SAME tau as the rooted-counting majorant, not an unrelated D metric.

The prefactor is independent of the cutoff/volume because the input constants
are quantified before the full family. No I7, new axiom or positive gap input. -/
theorem original33_connected_cluster_decay
    {κ σ ε Cnt Cgeo Crt dist : ℝ}
    (hασ : σ < κ) (hε : 0 ≤ ε) (hCnt : 0 ≤ Cnt)
    (hCgeo : 0 < Cgeo)
    (F : ℕ → Finset Cluster) (a : Cluster → ℂ)
    (hcount : ∀ n, ((F n).card : ℝ) ≤ Cnt * Real.exp (σ * (n : ℝ)))
    (hweight : ∀ n γ, γ ∈ F n → ‖a γ‖ ≤ ε * Real.exp (-κ * (n : ℝ)))
    (hphysicalTau : ∀ n γ, γ ∈ F n → dist ≤ Cgeo * (n : ℝ) + Crt)
    (Sfull Sleft Sright : ℂ)
    (hconnectedPartition : Sfull - Sleft * Sright =
       ∑' n : ℕ, crossLevel F a n) :
    ‖Sfull - Sleft*Sright‖ ≤
      ((ε * Cnt) / (1 - Real.exp (-(κ - σ))) *
        Real.exp (((κ - σ) / Cgeo) * Crt)) *
        Real.exp (-((κ - σ) / Cgeo) * dist) := by
  have hbound := (connected_cross_polymer_decay hασ hε hCnt
    hCgeo F a hcount hweight hphysicalTau).2
  rw [hconnectedPartition]
  calc
    ‖∑' n : ℕ, crossLevel F a n‖ ≤
       (ε * Cnt / (1 - Real.exp (-(κ - σ)))) *
          Real.exp (-((κ - σ) / Cgeo) * (dist - Crt)) := hbound
    _ = ((ε * Cnt / (1 - Real.exp (-(κ - σ)))) *
          Real.exp (((κ - σ) / Cgeo) * Crt)) *
          Real.exp (-((κ - σ) / Cgeo) * dist) := by
      have hexp : Real.exp (-((κ - σ) / Cgeo) * (dist - Crt)) =
          Real.exp (((κ - σ) / Cgeo) * Crt) *
            Real.exp (-((κ - σ) / Cgeo) * dist) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring

#print axioms original33_connected_cluster_decay
end YMUIC.ConditionalCluster

namespace YMUIC.ConditionalCluster
open Filter
open scoped Topology

/-- The paper's actual cluster property E4: the source families may translate
to infinite physical separation, but all polymer constants are chosen once,
independent of that translation, cutoff and volume. The exact connected-
partition identity and the tau/physical-distance dictionary stay visible.
This does NOT assume E4 or its exponential decay as an extra premise. -/
theorem original33_cluster_property_at_infinity
    {Cluster ι : Type*} {l : Filter ι}
    {κ σ ε Cnt Cgeo Crt : ℝ}
    (hασ : σ < κ) (hε : 0 ≤ ε) (hCnt : 0 ≤ Cnt)
    (hCgeo : 0 < Cgeo)
    (dist : ι → ℝ) (hdist : Tendsto dist l atTop)
    (F : ι → ℕ → Finset Cluster) (a : ι → Cluster → ℂ)
    (hcount : ∀ y n, ((F y n).card : ℝ) ≤ Cnt * Real.exp (σ*(n:ℝ)))
    (hweight : ∀ y n γ, γ ∈ F y n → ‖a y γ‖ ≤ ε*Real.exp (-κ*(n:ℝ)))
    (hphysicalTau : ∀ y n γ, γ ∈ F y n → dist y ≤ Cgeo*(n:ℝ)+Crt)
    (Sfull Sleft Sright : ι → ℂ)
    (hpartition : ∀ y, Sfull y - Sleft y * Sright y =
      ∑' n : ℕ, crossLevel (F y) (a y) n) :
    Tendsto (fun y => Sfull y - Sleft y * Sright y) l (𝓝 (0:ℂ)) := by
  let m : ℝ := (κ-σ)/Cgeo
  let C : ℝ := (ε*Cnt/(1-Real.exp (-(κ-σ)))) * Real.exp (m*Crt)
  have hm : 0 < m := div_pos (sub_pos.mpr hασ) hCgeo
  have hneg : -m < 0 := neg_neg_of_pos hm
  have htop : Tendsto (fun y => -m*dist y) l atBot := by
    simpa only [mul_comm] using (hdist.atTop_mul_const_of_neg hneg)
  have hexp : Tendsto (fun y => Real.exp (-m*dist y)) l (𝓝 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp htop
  have hmajor : Tendsto (fun y => C*Real.exp (-m*dist y)) l (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using hexp.const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) hmajor
  exact original33_connected_cluster_decay hασ hε hCnt hCgeo
    (F y) (a y) (hcount y) (hweight y) (hphysicalTau y)
    (Sfull y) (Sleft y) (Sright y) (hpartition y)

#print axioms original33_cluster_property_at_infinity
end YMUIC.ConditionalCluster
