import YMConditional.Original33_ClusterProperty

set_option autoImplicit false
noncomputable section
namespace YMUIC.ConditionalCluster

open Filter
open scoped Topology

/-- C29 Lemma 17.8 with the SAME cutoff-volume-weak-stop filter for every
finite Schwinger moment. Uniform finite-regulator polymer inputs are the
original ones; there is no new continuum cluster assumption.

The role of the unresolved genuine Wilson physical tau dictionary is
explicit: `hphysicalTau` is a separate theorem parameter, not proved by the
finite rooted-tree algebra. The connected partition/cumulant cancellation
identity is also an upstream model input, not a restatement of decay. -/
theorem original33_cutoff_to_continuum_E4
    {I Y Cluster : Type*} {l : Filter I} [l.NeBot]
    {κ σ ε Cnt Cgeo Crt : ℝ}
    (hασ : σ < κ) (hε : 0 ≤ ε) (hCnt : 0 ≤ Cnt)
    (hCgeo : 0 < Cgeo)
    (dist : Y → ℝ) (ly : Filter Y) (hDist : Tendsto dist ly atTop)
    (F : I → Y → ℕ → Finset Cluster) (a : I → Y → Cluster → ℂ)
    (hcount : ∀ i y n, ((F i y n).card : ℝ) ≤
        Cnt * Real.exp (σ * (n : ℝ)))
    (hweight : ∀ i y n γ, γ ∈ F i y n →
        ‖a i y γ‖ ≤ ε * Real.exp (-κ*(n:ℝ)))
    (hphysicalTau : ∀ i y n γ, γ ∈ F i y n →
        dist y ≤ Cgeo * (n : ℝ) + Crt)
    (Sfull_i Sleft_i Sright_i : I → Y → ℂ)
    (Sfull Sleft Sright : Y → ℂ)
    (hconnectedPartition : ∀ i y,
        Sfull_i i y - Sleft_i i y * Sright_i i y =
          ∑' n : ℕ, crossLevel (F i y) (a i y) n)
    (hfull : ∀ y, Tendsto (fun i => Sfull_i i y) l (𝓝 (Sfull y)))
    (hleft : ∀ y, Tendsto (fun i => Sleft_i i y) l (𝓝 (Sleft y)))
    (hright : ∀ y, Tendsto (fun i => Sright_i i y) l (𝓝 (Sright y))) :
    (∀ y,
       ‖Sfull y - Sleft y * Sright y‖ ≤
        ((ε * Cnt / (1 - Real.exp (-(κ - σ)))) *
           Real.exp (((κ - σ) / Cgeo) * Crt)) *
          Real.exp (-((κ - σ) / Cgeo) * dist y)) ∧
    Tendsto (fun y => Sfull y - Sleft y * Sright y)
      ly (𝓝 (0 : ℂ)) := by
  let m : ℝ := (κ - σ) / Cgeo
  let C : ℝ := (ε * Cnt / (1 - Real.exp (-(κ - σ)))) * Real.exp (m * Crt)
  have hbound : ∀ y,
      ‖Sfull y - Sleft y * Sright y‖ ≤ C * Real.exp (-m * dist y) := by
    intro y
    have ht := ((hfull y).sub ((hleft y).mul (hright y))).norm
    apply le_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro i
    exact original33_connected_cluster_decay hασ hε hCnt hCgeo
      (F i y) (a i y) (hcount i y) (hweight i y) (hphysicalTau i y)
      (Sfull_i i y) (Sleft_i i y) (Sright_i i y) (hconnectedPartition i y)
  have hm : 0 < m := div_pos (sub_pos.mpr hασ) hCgeo
  have hneg : -m < 0 := neg_neg_of_pos hm
  have htop : Tendsto (fun y => -m * dist y) ly atBot := by
    simpa only [mul_comm] using hDist.atTop_mul_const_of_neg hneg
  have hexp : Tendsto (fun y => Real.exp (-m*dist y)) ly (𝓝 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp htop
  have hmajor : Tendsto (fun y => C * Real.exp (-m * dist y))
      ly (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hexp.const_mul C
  refine ⟨hbound, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hmajor

#print axioms original33_cutoff_to_continuum_E4
end YMUIC.ConditionalCluster
