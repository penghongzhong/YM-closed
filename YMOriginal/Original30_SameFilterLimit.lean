import YMOriginal.Original34_OSII_ExternalInterface

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original30

/-! A single common filter of regulated joint functionals, if pointwise
convergent and uniformly seminorm-bounded, yields a continuous joint limit.
This does not prove that the actual physical regulator net converges. -/

theorem joint_same_filter_limit
    {ι : Type*} (l : Filter ι) [NeBot l]
    (T : ∀ r : ℕ, ι → YMUIC.Original34.JointTest r →L[ℂ] ℂ)
    (S : ∀ r : ℕ, YMUIC.Original34.JointTest r → ℂ)
    (q m : ℕ → ℕ) (C : ℕ → ℝ)
    (hlim : ∀ r f, Tendsto (fun i => T r i f) l (𝓝 (S r f)))
    (hbound : ∀ r i f, ‖T r i f‖ ≤ C r *
      YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f) :
    ∃ H : YMUIC.Original34.SchwingerHierarchy,
      (∀ r f, H.S r f = S r f) ∧
      ∀ r f, ‖H.S r f‖ ≤ C r *
        YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f := by
  have hb (r : ℕ) (f : YMUIC.Original34.JointTest r) :
      ‖S r f‖ ≤ C r * YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f :=
    le_of_tendsto (hlim r f).norm (Filter.Eventually.of_forall fun i => hbound r i f)
  have hadd (r : ℕ) (x y : YMUIC.Original34.JointTest r) :
      S r (x + y) = S r x + S r y := by
    apply tendsto_nhds_unique (hlim r (x + y))
    simpa only [map_add] using (hlim r x).add (hlim r y)
  have hsmul (r : ℕ) (c : ℂ) (x : YMUIC.Original34.JointTest r) :
      S r (c • x) = c • S r x := by
    apply tendsto_nhds_unique (hlim r (c • x))
    simpa only [map_smul] using (tendsto_const_nhds.smul (hlim r x))
  let L (r : ℕ) : YMUIC.Original34.JointTest r →ₗ[ℂ] ℂ :=
    { toFun := S r, map_add' := hadd r, map_smul' := hsmul r }
  have hc (r : ℕ) : Continuous (L r) := by
    apply continuous_of_continuousAt_zero
    have hp := (YMUIC.OSTensor.joint_schwartz_control r (q r) (m r)).1
    have hzero : Tendsto (fun f : YMUIC.Original34.JointTest r =>
        C r * YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f)
        (𝓝 0) (𝓝 0) := by
      have ht := (tendsto_const_nhds (x := C r)).mul (hp.continuousAt (x := 0))
      simpa only [map_zero, mul_zero] using ht
    have hs : Tendsto (L r) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm (fun f => hb r f) hzero
    change Tendsto (L r) (𝓝 0) (𝓝 (L r 0))
    simpa only [map_zero] using hs
  refine ⟨⟨fun r => ⟨L r, hc r⟩⟩, ?_, ?_⟩
  · intros; rfl
  · exact hb

#print axioms joint_same_filter_limit
end YMUIC.Original30
