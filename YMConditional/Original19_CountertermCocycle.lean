import YMConditional.Original19_SmallPerturbation

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace YMUIC.Counterterm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward-ordered actual source maps: M_(m-1) ... M_1 M_0. -/
def actualCocycle (M : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => 1
  | n + 1 => M n * actualCocycle M n

/-- The same ordered product as a genuine continuous linear equivalence. -/
def equivalenceCocycle (S : ℕ → E ≃L[ℝ] E) : ℕ → E ≃L[ℝ] E
  | 0 => ContinuousLinearEquiv.refl ℝ E
  | n + 1 => (equivalenceCocycle S n).trans (S n)

theorem equivalenceCocycle_coe (S : ℕ → E ≃L[ℝ] E) (M : ℕ → E →L[ℝ] E)
    {m : ℕ} (hS : ∀ j < m, (S j : E →L[ℝ] E) = M j) :
    (equivalenceCocycle S m : E →L[ℝ] E) = actualCocycle M m := by
  induction m with
  | zero => rfl
  | succ n ih =>
      have hn := ih (fun j hj => hS j (by omega))
      change (S n : E →L[ℝ] E) * (equivalenceCocycle S n : E →L[ℝ] E) = _
      rw [hS n (by omega), hn]
      rfl

/-- Inverse transpose, expressed basis-independently on the continuous dual. -/
def transportedSource (Z : E ≃L[ℝ] E) (J : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  J.comp (Z.symm : E →L[ℝ] E)

theorem dual_transport_pairing (Z : E ≃L[ℝ] E) (J : E →L[ℝ] ℝ) (v : E) :
    transportedSource Z J (Z v) = J v := by
  simp [transportedSource]

theorem dual_transport_step (Z S : E ≃L[ℝ] E) (J : E →L[ℝ] ℝ) :
    transportedSource (Z.trans S) J = transportedSource S (transportedSource Z J) := by
  ext v
  rfl

/-- The local jet lives in E, whereas the unlocalized activity lives in F. -/
def jetRemainder {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (extract : F →L[ℝ] E) (includeJet : E →L[ℝ] F) : F →L[ℝ] F :=
  1 - includeJet.comp extract

theorem jet_remainder_exact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (extract : F →L[ℝ] E) (includeJet : E →L[ℝ] F)
    (hjet : extract.comp includeJet = ContinuousLinearMap.id ℝ E) (x : F) :
    x = includeJet (extract x) + jetRemainder extract includeJet x ∧
      extract (jetRemainder extract includeJet x) = 0 := by
  constructor
  · simp [jetRemainder]
  · have hv := congrArg (fun f : E →L[ℝ] E => f (extract x)) hjet
    simpa [jetRemainder, map_sub] using sub_eq_zero.mpr hv.symm

/-- Local projection is idempotent; no larger/unbounded source space is used. -/
theorem local_projection_idempotent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (extract : F →L[ℝ] E) (includeJet : E →L[ℝ] F)
    (hjet : extract.comp includeJet = ContinuousLinearMap.id ℝ E) :
    (includeJet.comp extract).comp (includeJet.comp extract) = includeJet.comp extract := by
  ext x
  have hv := congrArg (fun f : E →L[ℝ] E => f (extract x)) hjet
  exact congrArg includeJet hv

/-- Complete original19 implication. The classical isomorphism is supplied by
original18. Equation297 is the explicit preceding source-modulus hypothesis.
The actual marked-remainder estimate is transported unchanged, not invented.
No I7, spectral calculus, continuum limit or cumulative Z-to-I premise occurs. -/
theorem original19_fixed_dimension_counterterm [CompleteSpace E] {ι : Type*}
    (M0 : E ≃L[ℝ] E) (M : ι → ℝ → E →L[ℝ] E)
    (ω : ℝ → ℝ) {gMax : ℝ} (hgMax : 0 < gMax)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i g, 0 < g → g ≤ gMax → ‖M i g - (M0 : E →L[ℝ] E)‖ ≤ ω g) :
    ∃ gD : ℝ, 0 < gD ∧ gD ≤ gMax ∧
      ∀ (m : ℕ) (index : ℕ → ι) (g : ℕ → ℝ),
        (∀ j < m, 0 < g j ∧ g j ≤ gD) →
        ∃ Z : E ≃L[ℝ] E,
          (Z : E →L[ℝ] E) = actualCocycle (fun j => M (index j) (g j)) m ∧
          (∀ j < m, ∃ S : E ≃L[ℝ] E,
            (S : E →L[ℝ] E) = M (index j) (g j) ∧
            ‖(S.symm : E →L[ℝ] E)‖ ≤ 2 * ‖(M0.symm : E →L[ℝ] E)‖ ∧
            (S.symm : E →L[ℝ] E) =
              (∑' n : ℕ, (-relativePerturbation M0 (M (index j) (g j))) ^ n) *
                (M0.symm : E →L[ℝ] E)) ∧
          (∀ (J : E →L[ℝ] ℝ) (v : E),
            transportedSource Z J (actualCocycle (fun j => M (index j) (g j)) m v) = J v) := by
  obtain ⟨gD, hgD, hgDm, hsmall⟩ := uniform_relative_smallness M0 M ω hgMax hω hmod
  refine ⟨gD, hgD, hgDm, ?_⟩
  intro m index g hweak
  let S : ℕ → E ≃L[ℝ] E := fun j =>
    if hj : j < m then
      sourceStepEquiv M0 (M (index j) (g j))
        (hsmall (index j) (g j) (hweak j hj).1 (hweak j hj).2)
    else ContinuousLinearEquiv.refl ℝ E
  have hS : ∀ j < m, (S j : E →L[ℝ] E) = M (index j) (g j) := by
    intro j hj
    simp [S, hj]
  refine ⟨equivalenceCocycle S m, equivalenceCocycle_coe S _ hS, ?_, ?_⟩
  · intro j hj
    have hs := hsmall (index j) (g j) (hweak j hj).1 (hweak j hj).2
    exact ⟨sourceStepEquiv M0 _ hs, sourceStepEquiv_coe _ _ hs,
      sourceStepEquiv_inverse_norm _ _ hs, sourceStepEquiv_inverse_formula _ _ hs⟩
  · intro J v
    rw [← equivalenceCocycle_coe S _ hS]
    exact dual_transport_pairing _ _ _

/-- Full activity reading: exact local mixing cancellation and preservation of
the named upstream remainder bound in the SAME activity/source spaces. -/
theorem counterterm_activity_identity {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (extract : F →L[ℝ] E) (includeJet : E →L[ℝ] F)
    (hjet : extract.comp includeJet = ContinuousLinearMap.id ℝ E)
    (Z : E ≃L[ℝ] E) (J : E →L[ℝ] ℝ) (x : F) {R : ℝ}
    (hR : ‖x - includeJet (extract x)‖ ≤ R) :
    transportedSource Z J (Z (extract x)) = J (extract x) ∧
      x = includeJet (extract x) + jetRemainder extract includeJet x ∧
      extract (jetRemainder extract includeJet x) = 0 ∧
      ‖jetRemainder extract includeJet x‖ ≤ R := by
  refine ⟨dual_transport_pairing _ _ _, (jet_remainder_exact _ _ hjet x).1,
    (jet_remainder_exact _ _ hjet x).2, ?_⟩
  simpa [jetRemainder] using hR


/-- Original19, including its exact local/remainder statement. The source space
is genuinely finite dimensional. The same Z is used for the actual ordered
product and for every source/activity pairing. No uniform bound on Z is assumed. -/
theorem original19_counterterm_block [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    (M0 : E ≃L[ℝ] E) (M : ι → ℝ → E →L[ℝ] E)
    (ω : ℝ → ℝ) {gMax : ℝ} (hgMax : 0 < gMax)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i g, 0 < g → g ≤ gMax → ‖M i g - (M0 : E →L[ℝ] E)‖ ≤ ω g)
    (extract : F →L[ℝ] E) (includeJet : E →L[ℝ] F)
    (hjet : extract.comp includeJet = ContinuousLinearMap.id ℝ E) :
    ∃ gD : ℝ, 0 < gD ∧ gD ≤ gMax ∧
      ∀ (m : ℕ) (index : ℕ → ι) (g : ℕ → ℝ),
        (∀ j < m, 0 < g j ∧ g j ≤ gD) →
        ∃ Z : E ≃L[ℝ] E,
          (Z : E →L[ℝ] E) = actualCocycle (fun j => M (index j) (g j)) m ∧
          (∀ j < m, ∃ S : E ≃L[ℝ] E,
            (S : E →L[ℝ] E) = M (index j) (g j) ∧
            ‖(S.symm : E →L[ℝ] E)‖ ≤ 2 * ‖(M0.symm : E →L[ℝ] E)‖ ∧
            (S.symm : E →L[ℝ] E) =
              (∑' n : ℕ, (-relativePerturbation M0 (M (index j) (g j))) ^ n) *
                (M0.symm : E →L[ℝ] E)) ∧
          ∀ (J : E →L[ℝ] ℝ) (x : F),
            transportedSource Z J
              (actualCocycle (fun j => M (index j) (g j)) m (extract x)) = J (extract x) ∧
            x = includeJet (extract x) + jetRemainder extract includeJet x ∧
            extract (jetRemainder extract includeJet x) = 0 ∧
            ∀ R : ℝ, ‖x - includeJet (extract x)‖ ≤ R →
              ‖jetRemainder extract includeJet x‖ ≤ R := by
  obtain ⟨gD, hgD, hgDm, hblock⟩ :=
    original19_fixed_dimension_counterterm M0 M ω hgMax hω hmod
  refine ⟨gD, hgD, hgDm, ?_⟩
  intro m index g hweak
  obtain ⟨Z, hZ, hsteps, hdual⟩ := hblock m index g hweak
  refine ⟨Z, hZ, hsteps, ?_⟩
  intro J x
  refine ⟨hdual J (extract x), (jet_remainder_exact _ _ hjet x).1,
    (jet_remainder_exact _ _ hjet x).2, ?_⟩
  intro R hR
  simpa [jetRemainder] using hR

end YMUIC.Counterterm
