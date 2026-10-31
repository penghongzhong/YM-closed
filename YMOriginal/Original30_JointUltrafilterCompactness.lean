import YMOriginal.Original30_SameFilterLimit

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original30

/-- A uniformly seminorm-bounded joint hierarchy has a common ultrafilter
limit for EVERY order and EVERY joint Schwartz test. No testwise limit,
dense test class, or countability assumption is an input. The ultrafilter
refines the prescribed regulator filter. Uniqueness is only for that fixed
ultrafilter; convergence along the original filter is not asserted. -/
theorem joint_ultrafilter_compactness
    {ι : Type*} (l : Filter ι) [NeBot l]
    (T : ∀ r : ℕ, ι → YMUIC.Original34.JointTest r →L[ℂ] ℂ)
    (q m : ℕ → ℕ) (C : ℕ → ℝ)
    (hbound : ∀ r i f, ‖T r i f‖ ≤ C r *
      YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f) :
    ∃ u : Ultrafilter ι, (u : Filter ι) ≤ l ∧
      ∃! H : YMUIC.Original34.SchwingerHierarchy,
        (∀ r f, Tendsto (fun i => T r i f) (u : Filter ι) (𝓝 (H.S r f))) ∧
        ∀ r f, ‖H.S r f‖ ≤ C r *
          YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f := by
  let u := Ultrafilter.of l
  have hlim (r : ℕ) (f : YMUIC.Original34.JointTest r) :
      ∃ z : ℂ, Tendsto (fun i => T r i f) (u : Filter ι) (𝓝 z) := by
    let B := Metric.closedBall (0 : ℂ)
      (C r * YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f)
    have hB : B ∈ u.map (fun i => T r i f) := by
      change {i | T r i f ∈ B} ∈ (u : Filter ι)
      apply Filter.Eventually.of_forall
      intro i
      simpa only [B, Metric.mem_closedBall, dist_zero_right] using hbound r i f
    obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) _).ultrafilter_le_nhds'
      (u.map (fun i => T r i f)) hB
    exact ⟨z, hz⟩
  choose s hs using hlim
  obtain ⟨H, heq, hb⟩ := joint_same_filter_limit (u : Filter ι) T s q m C hs hbound
  have hconv (r : ℕ) (f : YMUIC.Original34.JointTest r) :
      Tendsto (fun i => T r i f) (u : Filter ι) (𝓝 (H.S r f)) := by
    rw [heq]
    exact hs r f
  refine ⟨u, Ultrafilter.of_le l, H, ⟨hconv, hb⟩, ?_⟩
  intro H' hH'
  have hS : H'.S = H.S := by
    funext r
    ext f
    exact tendsto_nhds_unique (hH'.1 r f) (hconv r f)
  cases H
  cases H'
  congr

end YMUIC.Original30
