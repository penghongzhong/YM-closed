import YMOriginal.Original30_PolymerSourceMoments

set_option autoImplicit false
noncomputable section

open Metric Set Filter Topology

namespace YMUIC.Original30

/-!
The finite-volume normalized generating function can contain background
polymers that never meet the source support. If these are source-independent,
their contributions cancel exactly between H(J) and H(0). Hence the analytic
budget is needed only on the active set, not on the full volume. This is an
abstract locality reduction; the actual RG source locality, analytic radii,
uniform activity bounds and physical source dictionary remain model inputs.
-/

theorem local_polymer_source_normalized_moments
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : Finset ι) (active : ι → Prop) [DecidablePred active]
    (activity : ι → E → ℂ) (weight : ι → ℝ)
    {ρ A : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hlocal : ∀ i ∈ Γ, ¬ active i → ∀ J ∈ ball 0 ρ,
      activity i J = activity i 0)
    (hanalytic : ∀ i ∈ Γ.filter active,
      AnalyticOnNhd ℂ (activity i) (ball 0 ρ))
    (hweight : ∀ i ∈ Γ.filter active, ∀ J ∈ ball 0 ρ,
      ‖activity i J‖ ≤ weight i)
    (hbudget : ∑ i ∈ Γ.filter active, weight i ≤ A) :
    let Z : E → ℂ := fun J =>
      Complex.exp ((∑ i ∈ Γ, activity i J) - ∑ i ∈ Γ, activity i 0)
    AnalyticOnNhd ℂ Z (ball 0 ρ) ∧ Z 0 = 1 ∧
      ∀ (r : ℕ) (h : Fin r → E),
        ‖iteratedFDeriv ℂ r Z 0 h‖ ≤
          Real.exp 1 * (r.factorial : ℝ) *
            (Real.exp 1 * (1 + 2 * A) / ρ) ^ r * ∏ j, ‖h j‖ := by
  have heq (J : E) (hJ : J ∈ ball 0 ρ) :
      (∑ i ∈ Γ, activity i J) - ∑ i ∈ Γ, activity i 0 =
      (∑ i ∈ Γ.filter active, activity i J) -
        ∑ i ∈ Γ.filter active, activity i 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : active i
    · simp [ha]
    · simp [ha, hlocal i hi ha J hJ]
  have hZ : Set.EqOn (fun J : E =>
      Complex.exp ((∑ i ∈ Γ, activity i J) - ∑ i ∈ Γ, activity i 0))
      (fun J : E => Complex.exp ((∑ i ∈ Γ.filter active, activity i J) -
        ∑ i ∈ Γ.filter active, activity i 0)) (ball 0 ρ) := by
    intro J hJ
    dsimp only
    rw [heq J hJ]
  have hevent : (fun J : E =>
      Complex.exp ((∑ i ∈ Γ, activity i J) - ∑ i ∈ Γ, activity i 0))
      =ᶠ[𝓝 0] (fun J : E =>
        Complex.exp ((∑ i ∈ Γ.filter active, activity i J) -
          ∑ i ∈ Γ.filter active, activity i 0)) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hρ) hZ
  have hbase := polymer_source_normalized_moments
    (Γ.filter active) activity weight hρ hA hanalytic hweight hbudget
  refine ⟨hbase.1.congr isOpen_ball hZ.symm, ?_, ?_⟩
  · exact (hZ (mem_ball_self hρ)).trans hbase.2.1
  · intro r h
    rw [(hevent.iteratedFDeriv ℂ r).self_of_nhds]
    exact hbase.2.2 r h

#print axioms local_polymer_source_normalized_moments

end YMUIC.Original30
