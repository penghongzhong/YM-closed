import YM.Wilson.SourceCocycleChain21
import YM.Wilson.DualPairingAllD
import YM.Wilson.CandidateGramRoots21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-!
# C29 equation (304): left-ordered SU(2) RG and exact canonical dual

The manuscript defines Z_m = M_(m-1) ... M_0.  This is NOT the
right-growing sourceCocycleChain C m = C_0 ... C_(m-1) used for scalar
column bounds in earlier modules. The present file defines the exact
manuscript product, proves source action/composition, and derives the
canonical pairing for every finite RG depth from ONE-STEP inverse
transpose identities. Neither a cumulative inverse norm nor its
uniform bound is assumed.

No claim is made that the actual physical Yang--Mills M_(j,D) source
matrix or the normalized source is supplied by the current hypotheses.
-/

abbrev SourceRGMatrix21 := RootFiber21 → RootFiber21 → ℂ

/-- The 21-component primal or dual source action. -/
def sourceRGAction (C : SourceRGMatrix21)
    (v : RootFiber21 → ℂ) : RootFiber21 → ℂ :=
  fun i => ∑ j : RootFiber21, C i j * v j

theorem source_rg_action_identity (v : RootFiber21 → ℂ) :
    sourceRGAction sourceCocycleIdentity v = v := by
  classical
  funext i
  simp [sourceRGAction, sourceCocycleIdentity]

theorem source_rg_action_compose
    (C D : SourceRGMatrix21) (v : RootFiber21 → ℂ) :
    sourceRGAction (sourceCocycleCompose C D) v =
      sourceRGAction C (sourceRGAction D v) := by
  classical
  funext i
  calc
    sourceRGAction (sourceCocycleCompose C D) v i =
      ∑ j : RootFiber21, (∑ k : RootFiber21, C i k * D k j) * v j := rfl
    _ = ∑ j : RootFiber21, ∑ k : RootFiber21,
        (C i k * D k j) * v j := by simp_rw [Finset.sum_mul]
    _ = ∑ k : RootFiber21, ∑ j : RootFiber21,
        (C i k * D k j) * v j := by rw [Finset.sum_comm]
    _ = ∑ k : RootFiber21, ∑ j : RootFiber21,
        C i k * (D k j * v j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ k : RootFiber21,
        C i k * (∑ j : RootFiber21, D k j * v j) := by
          simp_rw [Finset.mul_sum]
    _ = sourceRGAction C (sourceRGAction D v) i := rfl

/-- Correct physical RG chronology: Z_(n+1) = C_n Z_n, so
Z_n=C_(n-1) ... C_0. -/
def leftOrderedSourceRGChain (C : ℕ → SourceRGMatrix21) :
    ℕ → SourceRGMatrix21
  | 0 => sourceCocycleIdentity
  | n + 1 => sourceCocycleCompose (C n) (leftOrderedSourceRGChain C n)

/-- The all-scale canonical pairing is DERIVED from exact one-step
dual relations, not assumed as an all-scale matrix hypothesis. -/
theorem source_paired_left_ordered_rg_chain
    (C B : ℕ → SourceRGMatrix21)
    (hstep : ∀ (n : ℕ) (k j : RootFiber21),
      (∑ i : RootFiber21, C n i k * B n i j) =
        if k = j then 1 else 0)
    (v J : RootFiber21 → ℂ) :
    ∀ n : ℕ,
      (∑ i : RootFiber21,
        sourceRGAction (leftOrderedSourceRGChain C n) v i *
          sourceRGAction (leftOrderedSourceRGChain B n) J i) =
      ∑ k : RootFiber21, v k * J k := by
  intro n
  induction n with
  | zero =>
      simp only [leftOrderedSourceRGChain, source_rg_action_identity]
  | succ n ih =>
      change
        (∑ i : RootFiber21,
          sourceRGAction
            (sourceCocycleCompose (C n) (leftOrderedSourceRGChain C n)) v i *
          sourceRGAction
            (sourceCocycleCompose (B n) (leftOrderedSourceRGChain B n)) J i) =
          ∑ k : RootFiber21, v k * J k
      simp only [source_rg_action_compose]
      exact (source_primal_dual_pairing_allD (C n) (B n)
        (hstep n) (sourceRGAction (leftOrderedSourceRGChain C n) v)
        (sourceRGAction (leftOrderedSourceRGChain B n) J)).trans ih

/-- Uniformity of the canonically PAIRED candidate 21-root Wilson
observable for ALL RG depths, with no cumulative source-norm hypothesis.
The model still must prove hstep and identify the physical normalized
sources with the candidate 21 roots. -/
theorem paired_candidate_gram_left_rg_uniform
    (C B : ℕ → SourceRGMatrix21)
    (hstep : ∀ (n : ℕ) (k j : RootFiber21),
      (∑ i : RootFiber21, C n i k * B n i j) =
        if k = j then 1 else 0)
    (J : RootFiber21 → ℂ)
    (U : GramPlaquette6 → YMUICV128.Section03.SU2)
    (position : RootFiber21 → Space4)
    (f : SchwartzMap Space4 ℂ) :
    ∀ n : ℕ,
      ‖∑ i : RootFiber21,
        sourceRGAction (leftOrderedSourceRGChain C n)
          (candidateGramSchwartzDirection U position f) i *
        sourceRGAction (leftOrderedSourceRGChain B n) J i‖ ≤
      4 * (∑ j : RootFiber21, ‖J j‖) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  intro n
  rw [source_paired_left_ordered_rg_chain C B hstep
    (candidateGramSchwartzDirection U position f) J n]
  have hsrc (j : RootFiber21) :
      ‖candidateGramSchwartzDirection U position f j‖ ≤
        4 * SchwartzMap.seminorm ℂ 0 0 f :=
    (norm_le_pi_norm (candidateGramSchwartzDirection U position f) j).trans
      (candidate_gram_schwartz_uniform U position f)
  calc
    ‖∑ j : RootFiber21,
        candidateGramSchwartzDirection U position f j * J j‖ ≤
      ∑ j : RootFiber21,
        ‖candidateGramSchwartzDirection U position f j * J j‖ :=
          norm_sum_le _ _
    _ = ∑ j : RootFiber21,
          ‖candidateGramSchwartzDirection U position f j‖ *
            ‖J j‖ := by simp only [norm_mul]
    _ ≤ ∑ j : RootFiber21,
          (4 * SchwartzMap.seminorm ℂ 0 0 f) * ‖J j‖ := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right (hsrc j) (norm_nonneg _)
    _ = 4 * (∑ j : RootFiber21, ‖J j‖) *
          SchwartzMap.seminorm ℂ 0 0 f := by
            rw [← Finset.mul_sum]
            ring

end YMUIC.Wilson
