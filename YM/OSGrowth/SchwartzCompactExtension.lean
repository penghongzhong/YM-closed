import YM.OSGrowth.SchwartzCompactDensity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.OSGrowth

/-- The actual compactly supported Schwartz tests, with inherited algebra. -/
def compactSchwartzSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℂ (SchwartzMap E ℂ) where
  carrier := {f | HasCompactSupport (f : E → ℂ)}
  zero_mem' := by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : E → ℂ))
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => hf.smul_left (f := fun _ => c)

/-- A linear functional defined only on actual compact tests extends
uniquely to all Schwartz tests under one continuous seminorm bound.
Continuity of the initial functional and density are both derived. -/
theorem compact_schwartz_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    (P : Seminorm ℂ (SchwartzMap E ℂ)) (hP : Continuous P) (C : ℝ)
    (L : compactSchwartzSubmodule E →ₗ[ℂ] ℂ)
    (hbound : ∀ f : compactSchwartzSubmodule E, ‖L f‖ ≤ C * P f) :
    ∃! S : SchwartzMap E ℂ →L[ℂ] ℂ,
      (∀ f : compactSchwartzSubmodule E, S f = L f) ∧
      ∀ f, ‖S f‖ ≤ C * P f := by
  let D := compactSchwartzSubmodule E
  let : IsUniformAddGroup D := D.toAddSubgroup.isUniformAddGroup
  have hc : Continuous L := by
    apply continuous_of_continuousAt_zero
    have ht : Tendsto (fun f : D => C * P f) (𝓝 0) (𝓝 0) := by
      have h := (tendsto_const_nhds (x := C)).mul
        ((hP.comp continuous_subtype_val).continuousAt (x := (0 : D)))
      simpa only [Function.comp_apply, Submodule.coe_zero, map_zero, mul_zero] using h
    have hzero : Tendsto L (𝓝 0) (𝓝 0) := squeeze_zero_norm hbound ht
    change Tendsto L (𝓝 0) (𝓝 (L 0))
    simpa only [map_zero] using hzero
  let LD : D →L[ℂ] ℂ := ⟨L, hc⟩
  let S : SchwartzMap E ℂ →L[ℂ] ℂ := LD.extend D.subtypeL
  have hdense : DenseRange D.subtypeL := by
    change Dense (Set.range (fun f : D => (f : SchwartzMap E ℂ)))
    simpa [D, compactSchwartzSubmodule] using
      (compact_support_schwartz_dense (E := E))
  have hind : IsUniformInducing D.subtypeL :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have he (f : D) : S f = L f := LD.extend_eq hdense hind f
  refine ⟨S, ⟨he, ?_⟩, ?_⟩
  · intro f
    obtain ⟨hs, ht⟩ := dyadic_schwartz_approximation f
    have hb (n : ℕ) : ‖S (dyadicSchwartzCutoff n f)‖ ≤
        C * P (dyadicSchwartzCutoff n f) := by
      rw [he ⟨dyadicSchwartzCutoff n f, hs n⟩]
      exact hbound ⟨dyadicSchwartzCutoff n f, hs n⟩
    exact le_of_tendsto_of_tendsto ((S.continuous.tendsto f).comp ht).norm
      (((hP.tendsto f).comp ht).const_mul C) (Eventually.of_forall hb)
  · intro S' hS'
    apply (LD.extend_unique hdense hind S' ?_).symm
    ext f
    exact hS'.1 f

end YMUIC.OSGrowth
