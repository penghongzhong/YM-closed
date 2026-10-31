import YMOriginal.Original30_DenseTestLimit

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.Original30

/-!
All-order joint limit from atoms on one regulator filter. Only convergence
on the atom set is supplied; finite linear combinations, all joint tests,
continuity, uniqueness and preservation of the bound are derived. Density
of the chosen atom span and the regulated joint estimate remain explicit.
-/

theorem joint_atom_same_filter_limit
    {ι : Type*} (l : Filter ι) [NeBot l]
    (T : ∀ r : ℕ, ι → YMUIC.Original34.JointTest r →L[ℂ] ℂ)
    (A : ∀ r : ℕ, Set (YMUIC.Original34.JointTest r))
    (hA : ∀ r, Dense (Submodule.span ℂ (A r) :
      Set (YMUIC.Original34.JointTest r)))
    (q m : ℕ → ℕ) (C : ℕ → ℝ)
    (hlim : ∀ r f, f ∈ A r → ∃ z : ℂ,
      Tendsto (fun i => T r i f) l (𝓝 z))
    (hbound : ∀ r i f, ‖T r i f‖ ≤ C r *
      YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f) :
    ∃! H : YMUIC.Original34.SchwingerHierarchy,
      (∀ r f, Tendsto (fun i => T r i f) l (𝓝 (H.S r f))) ∧
      ∀ r f, ‖H.S r f‖ ≤ C r *
        YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f := by
  have hspan (r : ℕ) (f : Submodule.span ℂ (A r)) :
      ∃ z : ℂ, Tendsto (fun i => T r i f) l (𝓝 z) := by
    rcases f with ⟨f, hmem⟩
    change ∃ z : ℂ, Tendsto (fun i => T r i f) l (𝓝 z)
    induction hmem using Submodule.span_induction with
    | mem f hf => exact hlim r f hf
    | zero => exact ⟨0, by simpa only [map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℂ)) l (𝓝 0))⟩
    | add f g _ _ hf hg =>
      obtain ⟨z, hz⟩ := hf
      obtain ⟨w, hw⟩ := hg
      exact ⟨z + w, by simpa only [map_add] using hz.add hw⟩
    | smul c f _ hf =>
      obtain ⟨z, hz⟩ := hf
      exact ⟨c • z, by simpa only [map_smul] using tendsto_const_nhds.smul hz⟩
  have hex (r : ℕ) : ∃ S : YMUIC.Original34.JointTest r →L[ℂ] ℂ,
      (∀ f, Tendsto (fun i => T r i f) l (𝓝 (S f))) ∧
      ∀ f, ‖S f‖ ≤ C r *
        YMUIC.OSTensor.jointSchwartzControl r (q r) (m r) f :=
    (dense_test_same_filter_limit l r (q r) (m r) (C r) (T r)
      (Submodule.span ℂ (A r)) (hA r) (hspan r) (hbound r)).exists
  choose S hS using hex
  let H : YMUIC.Original34.SchwingerHierarchy := ⟨S⟩
  refine ⟨H, ⟨fun r => (hS r).1, fun r => (hS r).2⟩, ?_⟩
  intro H' hH'
  have he : H'.S = H.S := by
    funext r
    ext f
    exact tendsto_nhds_unique (hH'.1 r f) ((hS r).1 f)
  exact congrArg YMUIC.Original34.SchwingerHierarchy.mk he

end YMUIC.Original30
