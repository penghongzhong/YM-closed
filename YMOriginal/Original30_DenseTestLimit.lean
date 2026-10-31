import YMOriginal.Original34_OSII_ExternalInterface
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original30

/-!
Upgrade convergence on a dense linear test class to convergence on ALL
joint Schwartz tests along the SAME regulator filter. No limit on general
tests is assumed. The dense class, uniform bound and convergence on that
class remain explicit inputs; this does not construct the physical RG net.
-/

theorem dense_test_same_filter_limit
    {ι : Type*} (l : Filter ι) [NeBot l]
    (r q m : ℕ) (C : ℝ)
    (T : ι → YMUIC.Original34.JointTest r →L[ℂ] ℂ)
    (D : Submodule ℂ (YMUIC.Original34.JointTest r))
    (hD : Dense (D : Set (YMUIC.Original34.JointTest r)))
    (hlim : ∀ d : D, ∃ z : ℂ, Tendsto (fun i => T i d) l (𝓝 z))
    (hbound : ∀ i f, ‖T i f‖ ≤ C *
      YMUIC.OSTensor.jointSchwartzControl r q m f) :
    ∃! S : YMUIC.Original34.JointTest r →L[ℂ] ℂ,
      (∀ f, Tendsto (fun i => T i f) l (𝓝 (S f))) ∧
      ∀ f, ‖S f‖ ≤ C * YMUIC.OSTensor.jointSchwartzControl r q m f := by
  let : IsUniformAddGroup D := D.toAddSubgroup.isUniformAddGroup
  choose s hs using hlim
  let P := YMUIC.OSTensor.jointSchwartzControl r q m
  have hp : Continuous P :=
    (YMUIC.OSTensor.joint_schwartz_control r q m).1
  have hb (d : D) : ‖s d‖ ≤ C * P d :=
    le_of_tendsto (hs d).norm (Filter.Eventually.of_forall fun i => hbound i d)
  have hadd (x y : D) : s (x + y) = s x + s y := by
    apply tendsto_nhds_unique (hs (x + y))
    simpa only [Submodule.coe_add, map_add] using (hs x).add (hs y)
  have hsmul (c : ℂ) (x : D) : s (c • x) = c • s x := by
    apply tendsto_nhds_unique (hs (c • x))
    simpa only [Submodule.coe_smul, map_smul] using
      (tendsto_const_nhds.smul (hs x))
  let L : D →ₗ[ℂ] ℂ :=
    { toFun := s, map_add' := hadd, map_smul' := hsmul }
  have hc : Continuous L := by
    apply continuous_of_continuousAt_zero
    have hzero : Tendsto (fun d : D => C * P d) (𝓝 0) (𝓝 0) := by
      have ht := (tendsto_const_nhds (x := C)).mul
        ((hp.comp continuous_subtype_val).continuousAt (x := (0 : D)))
      simpa only [Function.comp_apply, Submodule.coe_zero, map_zero, mul_zero] using ht
    have hs0 : Tendsto L (𝓝 0) (𝓝 0) := squeeze_zero_norm hb hzero
    change Tendsto L (𝓝 0) (𝓝 (L 0))
    simpa only [map_zero] using hs0
  let LD : D →L[ℂ] ℂ := ⟨L, hc⟩
  let S : YMUIC.Original34.JointTest r →L[ℂ] ℂ := LD.extend D.subtypeL
  have hdense : DenseRange D.subtypeL := by
    change Dense (Set.range (fun d : D => (d : YMUIC.Original34.JointTest r)))
    simpa using hD
  have hind : IsUniformInducing D.subtypeL :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have hSD (d : D) : S d = s d := LD.extend_eq hdense hind d
  have hEq : Equicontinuous (fun i f => T i f) := by
    intro x
    have hzero : Tendsto (fun y => C * P (x - y)) (𝓝 x) (𝓝 0) := by
      have hsub : Continuous (fun y : YMUIC.Original34.JointTest r => x - y) :=
        continuous_const.sub continuous_id
      have ht := (tendsto_const_nhds (x := C)).mul
        ((hp.comp hsub).continuousAt (x := x))
      simpa only [Function.comp_apply, sub_self, map_zero, mul_zero] using ht
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun y => C * P (x - y)) hzero (fun i f => T i f)
    exact Filter.Eventually.of_forall fun y i => by
      rw [dist_eq_norm, ← map_sub]
      exact hbound i (x - y)
  have hconv (f : YMUIC.Original34.JointTest r) :
      Tendsto (fun i => T i f) l (𝓝 (S f)) := by
    apply (hEq f).tendsto_of_mem_closure S.continuous.continuousWithinAt
      (s := (D : Set (YMUIC.Original34.JointTest r)))
    · intro y hy
      simpa only [hSD ⟨y, hy⟩] using hs ⟨y, hy⟩
    · exact hD f
  refine ⟨S, ⟨hconv, ?_⟩, ?_⟩
  · intro f
    exact le_of_tendsto (hconv f).norm
      (Filter.Eventually.of_forall fun i => hbound i f)
  · intro S' hS'
    ext f
    exact tendsto_nhds_unique (hS'.1 f) (hconv f)

end YMUIC.Original30
