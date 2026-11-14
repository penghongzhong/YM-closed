import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30

/-!
# v116 joint cutoff--volume Cauchy assembly

This is the scalar completeness/triangle-inequality part of the v116 C1
argument.  The model-specific inputs remain separate:
* fixed-volume phase-locked UV Cauchy (v115);
* cutoff-uniform volume/exhaustion tail from rooted locality (v57/CMP119).

The theorem does not assume the desired joint limit.
-/

/-- Fixed-volume UV Cauchy plus a UV-uniform large-volume comparison gives
a genuine two-parameter Cauchy criterion.  The reference volume can be
chosen after epsilon and before the UV depth, exactly as in v116. -/
theorem v116_joint_cutoff_volume_cauchy_criterion
    (S : ℕ → ℕ → ℂ)
    (hVolume : ∀ ε : ℝ, 0 < ε →
      ∃ M0 : ℕ, ∀ N M : ℕ, M0 ≤ M →
        ‖S N M - S N M0‖ < ε)
    (hUV : ∀ M : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        ‖S N M - S N' M‖ < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N0 M0 : ℕ,
        ∀ N N' M M' : ℕ,
          N0 ≤ N → N0 ≤ N' → M0 ≤ M → M0 ≤ M' →
          ‖S N M - S N' M'‖ < ε := by
  intro ε hε
  obtain ⟨M0, hM0⟩ := hVolume (ε / 3) (by linarith)
  obtain ⟨N0, hN0⟩ := hUV M0 (ε / 3) (by linarith)
  refine ⟨N0, M0, ?_⟩
  intro N N' M M' hN hN' hM hM'
  have hleft := hM0 N M hM
  have hmid := hN0 N N' hN hN'
  have hright := hM0 N' M' hM'
  calc
    ‖S N M - S N' M'‖
        ≤ ‖S N M - S N M0‖ +
          ‖S N M0 - S N' M0‖ +
          ‖S N' M0 - S N' M'‖ := by
            calc
              ‖S N M - S N' M'‖
                  ≤ ‖S N M - S N M0‖ +
                    ‖S N M0 - S N' M'‖ := by
                      simpa [sub_eq_add_neg, add_assoc] using
                        norm_add_le
                          (S N M - S N M0)
                          (S N M0 - S N' M')
              _ ≤ ‖S N M - S N M0‖ +
                    (‖S N M0 - S N' M0‖ +
                      ‖S N' M0 - S N' M'‖) := by
                      gcongr
                      simpa [sub_eq_add_neg, add_assoc] using
                        norm_add_le
                          (S N M0 - S N' M0)
                          (S N' M0 - S N' M')
              _ = _ := by ring
    _ < ε := by
      have hright' : ‖S N' M0 - S N' M'‖ < ε / 3 := by
        rw [norm_sub_rev]
        exact hright
      linarith

/-- If the volume comparison is itself pairwise rather than relative to a
chosen reference exhaustion, the joint criterion is an immediate corollary. -/
theorem v116_joint_cutoff_volume_cauchy_of_pairwise_tail
    (S : ℕ → ℕ → ℂ)
    (hVolumePair : ∀ ε : ℝ, 0 < ε →
      ∃ M0 : ℕ, ∀ N M M' : ℕ, M0 ≤ M → M0 ≤ M' →
        ‖S N M - S N M'‖ < ε)
    (hUV : ∀ M : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        ‖S N M - S N' M‖ < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N0 M0 : ℕ,
        ∀ N N' M M' : ℕ,
          N0 ≤ N → N0 ≤ N' → M0 ≤ M → M0 ≤ M' →
          ‖S N M - S N' M'‖ < ε := by
  apply v116_joint_cutoff_volume_cauchy_criterion S
  · intro ε hε
    obtain ⟨M0, hM0⟩ := hVolumePair ε hε
    refine ⟨M0, ?_⟩
    intro N M hM
    exact hM0 N M M0 hM le_rfl
  · exact hUV

#print axioms v116_joint_cutoff_volume_cauchy_criterion
#print axioms v116_joint_cutoff_volume_cauchy_of_pairwise_tail

end YMUIC.Original30
