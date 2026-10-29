import YM.Wilson.WordSource
import YM.Wilson.SourceMix21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# A new explicit 21-component SU(2) Gram-root candidate

This module is an INDEPENDENT reconstruction, not the missing archived
early C-stage v111.  The candidate uses six shared-basepoint plaquette
holonomies indexed by 2-form directions (12,13,14,23,24,34) and the 21
unordered index pairs. The gauge/jet/normalization correspondence to
the actual v111/v118 source is NOT proved here.

For W(U) = 2 - Re Tr U, define
  R_ij = (W(U_i U_j) - W(U_i) - W(U_j))/2.
Algebraically this equals -1/2 Re Tr((U_i-I)(U_j-I)).
All bounds below are for actual SU(2) values, not abstract source
surrogates.
-/

abbrev GramPlaquette6 := Fin 6

/-- A real, bounded SU(2) cross-plaquette Wilson root. -/
def candidateGramRoot (U : GramPlaquette6 → SU2)
    (i j : GramPlaquette6) : ℝ :=
  (wilsonRoot (U i * U j) - wilsonRoot (U i) -
    wilsonRoot (U j)) / 2

theorem candidate_gram_root_bounds
    (U : GramPlaquette6 → SU2) (i j : GramPlaquette6) :
    -4 ≤ candidateGramRoot U i j ∧ candidateGramRoot U i j ≤ 2 := by
  obtain ⟨hp0, hp4⟩ := wilsonRoot_bounds (U i * U j)
  obtain ⟨hi0, hi4⟩ := wilsonRoot_bounds (U i)
  obtain ⟨hj0, hj4⟩ := wilsonRoot_bounds (U j)
  unfold candidateGramRoot
  constructor <;> linarith

theorem candidate_gram_root_abs_le_four
    (U : GramPlaquette6 → SU2) (i j : GramPlaquette6) :
    |candidateGramRoot U i j| ≤ 4 := by
  obtain ⟨hl, hu⟩ := candidate_gram_root_bounds U i j
  exact abs_le.mpr ⟨hl, by linarith⟩

/-- Exactly the 21 upper-triangular pairs of the six physical 2-form
directions, in the independent reconstruction's fixed order. -/
def candidateGramPairs21 : Fin 21 → GramPlaquette6 × GramPlaquette6 :=
  ![(0,0), (0,1), (0,2), (0,3), (0,4), (0,5),
    (1,1), (1,2), (1,3), (1,4), (1,5),
    (2,2), (2,3), (2,4), (2,5),
    (3,3), (3,4), (3,5),
    (4,4), (4,5),
    (5,5)]

theorem candidate_gram_pairs_order :
    ∀ α : Fin 21,
      (candidateGramPairs21 α).1 ≤ (candidateGramPairs21 α).2 := by
  decide

theorem candidate_gram_pairs_injective :
    Function.Injective candidateGramPairs21 := by
  decide

/-- The explicit 21-component candidate, each component constructed
from TWO actual SU(2) plaquette values. -/
def candidateGramRoot21
    (U : GramPlaquette6 → SU2) (α : RootFiber21) : ℝ :=
  candidateGramRoot U
    (candidateGramPairs21 α).1 (candidateGramPairs21 α).2

theorem candidate_gram_root21_abs_le_four
    (U : GramPlaquette6 → SU2) (α : RootFiber21) :
    |candidateGramRoot21 U α| ≤ 4 :=
  candidate_gram_root_abs_le_four U
    (candidateGramPairs21 α).1 (candidateGramPairs21 α).2

/-- Source of the reconstructed Gram-root candidate, sampled at its
actual spacetime location, with no assumed abstract source bound. -/
def candidateGramSchwartzDirection
    (U : GramPlaquette6 → SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) : RootFiber21 → ℂ :=
  fun α => f (position α) * (candidateGramRoot21 U α : ℂ)

/-- Uniform bare 21-root Schwartz source bound, independent of lattice
positions, UV cutoff, volume and the six SU(2) holonomies. -/
theorem candidate_gram_schwartz_uniform
    (U : GramPlaquette6 → SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ‖candidateGramSchwartzDirection U position f‖ ≤
       4 * SchwartzMap.seminorm ℂ 0 0 f := by
  have hnonneg : 0 ≤ 4 * SchwartzMap.seminorm ℂ 0 0 f :=
    mul_nonneg (by norm_num) (apply_nonneg _ _)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro α
  have hw : ‖(candidateGramRoot21 U α : ℂ)‖ ≤ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact candidate_gram_root21_abs_le_four U α
  have hf : ‖f (position α)‖ ≤
      SchwartzMap.seminorm ℂ 0 0 f :=
    f.norm_le_seminorm ℂ (position α)
  calc
    ‖candidateGramSchwartzDirection U position f α‖ =
        ‖f (position α)‖ * ‖(candidateGramRoot21 U α : ℂ)‖ := by
          simp only [candidateGramSchwartzDirection, norm_mul]
    _ ≤ SchwartzMap.seminorm ℂ 0 0 f * 4 :=
      mul_le_mul hf hw (norm_nonneg _) (apply_nonneg _ _)
    _ = 4 * SchwartzMap.seminorm ℂ 0 0 f := by ring

/-- The exact 21-component mixing action on the reconstructed bare Gram
roots; the cumulative physical RG matrix is not assumed bounded. -/
def mixedCandidateGramSchwartz
    (B : RootFiber21 → RootFiber21 → ℂ)
    (U : GramPlaquette6 → SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) : RootFiber21 → ℂ :=
  fun α => ∑ j : RootFiber21,
    B j α * candidateGramSchwartzDirection U position f j

/-- A bound on the finite source mixing column sums implies a bound
for the explicit candidate Gram-root source without a spurious factor 21.
This is an algebraic conditional estimate, NOT an RG dynamical bound. -/
theorem mixed_candidate_gram_uniform
    (B : RootFiber21 → RootFiber21 → ℂ)
    (U : GramPlaquette6 → SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hcol : ∀ α : RootFiber21,
      (∑ j : RootFiber21, ‖B j α‖) ≤ K) :
    ‖mixedCandidateGramSchwartz B U position f‖ ≤
        4 * K * SchwartzMap.seminorm ℂ 0 0 f := by
  have hpi :
      ∀ j : RootFiber21,
        ‖candidateGramSchwartzDirection U position f j‖ ≤
          4 * SchwartzMap.seminorm ℂ 0 0 f := by
    intro j
    have htotal := candidate_gram_schwartz_uniform U position f
    exact (norm_le_pi_norm (candidateGramSchwartzDirection U position f) j).trans htotal
  have hp : 0 ≤ SchwartzMap.seminorm ℂ 0 0 f := apply_nonneg _ _
  have hrhs : 0 ≤ 4 * K * SchwartzMap.seminorm ℂ 0 0 f := by positivity
  apply (pi_norm_le_iff_of_nonneg hrhs).2
  intro α
  calc
    ‖mixedCandidateGramSchwartz B U position f α‖ ≤
      ∑ j : RootFiber21,
        ‖B j α * candidateGramSchwartzDirection U position f j‖ := by
          exact norm_sum_le _ _
    _ = ∑ j : RootFiber21,
          ‖B j α‖ * ‖candidateGramSchwartzDirection U position f j‖ := by
            simp only [norm_mul]
    _ ≤ ∑ j : RootFiber21,
          ‖B j α‖ * (4 * SchwartzMap.seminorm ℂ 0 0 f) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hpi j) (norm_nonneg _)
    _ = (∑ j : RootFiber21, ‖B j α‖) *
          (4 * SchwartzMap.seminorm ℂ 0 0 f) := by rw [Finset.sum_mul]
    _ ≤ K * (4 * SchwartzMap.seminorm ℂ 0 0 f) :=
          mul_le_mul_of_nonneg_right (hcol α) (mul_nonneg (by norm_num) hp)
    _ = 4 * K * SchwartzMap.seminorm ℂ 0 0 f := by ring

end YMUIC.Wilson
