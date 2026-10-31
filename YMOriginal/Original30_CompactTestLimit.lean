import YMOriginal.Original30_AtomHierarchyLimit
import YM.OSGrowth.SchwartzCompactExtension

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original30

/-- Starting with linear functionals defined ONLY on actual compactly
supported joint tests, derive their continuous Schwartz extensions and a
unique full hierarchy on the original common regulator filter. Density,
continuity, and convergence on general Schwartz tests are not hypotheses.
The single bound must be independent of the compact support: arbitrary
support-dependent constants do not supply this premise. -/
theorem joint_compact_same_filter_limit
    {ι : Type*} (l : Filter ι) [NeBot l]
    (L : ∀ r : ℕ, ι → YMUIC.OSGrowth.compactSchwartzSubmodule
      (EuclideanSpace ℝ (Fin (4 * r))) →ₗ[ℂ] ℂ)
    (q m : ℕ → ℕ) (C : ℕ → ℝ)
    (hlim : ∀ r (f : YMUIC.OSGrowth.compactSchwartzSubmodule
      (EuclideanSpace ℝ (Fin (4 * r)))),
        ∃ z : ℂ, Tendsto (fun i => L r i f) l (𝓝 z))
    (hbound : ∀ r i (f : YMUIC.OSGrowth.compactSchwartzSubmodule
      (EuclideanSpace ℝ (Fin (4 * r)))),
        ‖L r i f‖ ≤ C r * YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f) :
    ∃ T : ∀ r : ℕ, ι → YMUIC.Original34.JointTest r →L[ℂ] ℂ,
      (∀ r i (f : YMUIC.OSGrowth.compactSchwartzSubmodule
        (EuclideanSpace ℝ (Fin (4 * r)))), T r i f = L r i f) ∧
      (∀ r i f, ‖T r i f‖ ≤ C r *
        YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f) ∧
      ∃! H : YMUIC.Original34.SchwingerHierarchy,
        (∀ r f, Tendsto (fun i => T r i f) l (𝓝 (H.S r f))) ∧
        ∀ r f, ‖H.S r f‖ ≤ C r *
          YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f := by
  have hex (r : ℕ) (i : ι) : ∃ S : YMUIC.Original34.JointTest r →L[ℂ] ℂ,
      (∀ f : YMUIC.OSGrowth.compactSchwartzSubmodule
        (EuclideanSpace ℝ (Fin (4 * r))), S f = L r i f) ∧
      ∀ f, ‖S f‖ ≤ C r *
        YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f :=
    (YMUIC.OSGrowth.compact_schwartz_extension
      (YMUIC.OSTensor.jointSchwartzControl r (q r) (m r))
      (YMUIC.OSTensor.joint_schwartz_control r (q r) (m r)).1
      (C r) (L r i) (hbound r i)).exists
  choose T hT using hex
  refine ⟨T, (fun r i => (hT r i).1), (fun r i => (hT r i).2), ?_⟩
  let A (r : ℕ) : Set (YMUIC.Original34.JointTest r) :=
    {f | HasCompactSupport (f : EuclideanSpace ℝ (Fin (4 * r)) → ℂ)}
  have hA (r : ℕ) : Dense (Submodule.span ℂ (A r) :
      Set (YMUIC.Original34.JointTest r)) :=
    YMUIC.OSGrowth.compact_support_schwartz_dense.mono Submodule.subset_span
  apply joint_atom_same_filter_limit l T A hA q m C ?_
    (fun r i => (hT r i).2)
  intro r f hf
  obtain ⟨z, hz⟩ := hlim r ⟨f, hf⟩
  refine ⟨z, ?_⟩
  have he : (fun i => T r i f) = fun i => L r i ⟨f, hf⟩ :=
    funext fun i => (hT r i).1 ⟨f, hf⟩
  rwa [he]

end YMUIC.Original30
