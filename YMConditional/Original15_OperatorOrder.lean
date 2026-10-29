import YMConditional.Original15_GramTransfer
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace YMUIC.ConditionalI7
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine vacuum-orthogonal Hilbert subspace. -/
def vacuumSector (Ω : H) : Submodule ℂ H := (ℂ ∙ Ω)ᗮ

instance vacuumSector_complete (Ω : H) : CompleteSpace (vacuumSector Ω) := by
  unfold vacuumSector
  infer_instance

theorem transfer_preserves_vacuumSector (Ω : H) (T : H →L[ℂ] H)
    (hsym : IsSelfAdjoint T) (hfix : T Ω = Ω) :
    ∀ x ∈ vacuumSector Ω, T x ∈ vacuumSector Ω := by
  intro x hx
  rw [vacuumSector, Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  calc
    ⟪Ω, T x⟫_ℂ = ⟪T Ω, x⟫_ℂ :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsym Ω x).symm
    _ = ⟪Ω, x⟫_ℂ := by rw [hfix]
    _ = 0 := hx

def vacuumTransfer (Ω : H) (T : H →L[ℂ] H)
    (hsym : IsSelfAdjoint T) (hfix : T Ω = Ω) :
    vacuumSector Ω →L[ℂ] vacuumSector Ω :=
  (T.comp (vacuumSector Ω).subtypeL).codRestrict (vacuumSector Ω)
    (fun x => transfer_preserves_vacuumSector Ω T hsym hfix x.val x.property)

theorem vacuumTransfer_symmetric (Ω : H) (T : H →L[ℂ] H)
    (hsym : IsSelfAdjoint T) (hfix : T Ω = Ω) :
    IsSelfAdjoint (vacuumTransfer Ω T hsym hfix) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsym x.val y.val

/-- Full original #15 in Mathlib's actual Loewner operator order.
I7 is the finite Gram deficit assumption; the physical operator is positive,
fixes the vacuum, and acts on the actual orthogonal complement. -/
theorem original15_loewner_from_I7
    (Ω : H) (v : ι → H) (T : H →L[ℂ] H) (η : ℝ)
    (hT : T.IsPositive) (hfix : T Ω = Ω)
    (hdense : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (hI7 : I7Gram (fun i => center Ω (v i)) T η) :
    0 ≤ vacuumTransfer Ω T hT.isSelfAdjoint hfix ∧
      vacuumTransfer Ω T hT.isSelfAdjoint hfix ≤
        ((1 - η : ℝ) : ℂ) • (1 : vacuumSector Ω →L[ℂ] vacuumSector Ω) := by
  let R := vacuumTransfer Ω T hT.isSelfAdjoint hfix
  have hsR : IsSelfAdjoint R := vacuumTransfer_symmetric Ω T hT.isSelfAdjoint hfix
  constructor
  · apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    refine ⟨hsR, ?_⟩
    intro x
    exact hT.inner_nonneg_left x.val
  · apply (ContinuousLinearMap.le_def _ _).mpr
    constructor
    · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      apply LinearMap.IsSymmetric.sub
      · exact LinearMap.IsSymmetric.id.smul (by simp)
      · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsR
    · intro x
      have hx : ⟪Ω, x.val⟫_ℂ = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
      have h := original15_transfer_from_I7 Ω v T η hdense hI7 x.val hx
      change 0 ≤ (⟪((1 - η : ℝ) : ℂ) • x.val - T x.val, x.val⟫_ℂ).re
      rw [show (⟪((1 - η : ℝ) : ℂ) • x.val - T x.val, x.val⟫_ℂ).re =
        (⟪x.val, ((1 - η : ℝ) : ℂ) • x.val - T x.val⟫_ℂ).re from
        inner_re_symm (𝕜 := ℂ) _ _]
      rw [inner_sub_right, inner_smul_right, Complex.sub_re]
      have hn : (⟪x.val, x.val⟫_ℂ).re = ‖x.val‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) x.val
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hn]
      linarith


omit [CompleteSpace H] in
/-- The centering used in the Gram matrices is genuinely vacuum-orthogonal
when the physical vacuum is normalized. -/
theorem center_mem_vacuumSector (Ω x : H) (hΩ : ‖Ω‖ = 1) :
    center Ω x ∈ vacuumSector Ω := by
  rw [vacuumSector, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hself : ⟪Ω, Ω⟫_ℂ = 1 := by
    simpa [hΩ] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Ω)
  simp [center, inner_sub_right, inner_smul_right, hself]

/-- Original #15 with the strict uniform I7 range displayed in its output. -/
theorem original15_strict_transfer_from_I7
    (Ω : H) (v : ι → H) (T : H →L[ℂ] H) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hT : T.IsPositive) (hfix : T Ω = Ω)
    (hdense : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (hI7 : I7Gram (fun i => center Ω (v i)) T η) :
    0 < 1 - η ∧ 1 - η < 1 ∧
      0 ≤ vacuumTransfer Ω T hT.isSelfAdjoint hfix ∧
      vacuumTransfer Ω T hT.isSelfAdjoint hfix ≤
        ((1 - η : ℝ) : ℂ) • (1 : vacuumSector Ω →L[ℂ] vacuumSector Ω) := by
  exact ⟨by linarith, by linarith,
    original15_loewner_from_I7 Ω v T η hT hfix hdense hI7⟩

#print axioms original15_loewner_from_I7
#print axioms original15_strict_transfer_from_I7
end YMUIC.ConditionalI7
