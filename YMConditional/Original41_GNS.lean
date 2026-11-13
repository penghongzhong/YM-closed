import YMConditional.Original41_MomentLimit
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

noncomputable section
namespace YMUIC.ConditionalI7
open Filter MeasureTheory
open scoped Topology InnerProductSpace ComplexConjugate

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Defining inner-product identification of a GNS realization. No
nontriviality, variance lower bound, or spectral gap is included here. -/
def GNSPairing (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H) : Prop :=
  ∀ a b : A, ⟪J a, J b⟫_ℂ = ω (star a * b)

theorem gns_unit_inner (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1) :
    ⟪J 1, J 1⟫_ℂ = 1 := by
  simpa [star_one, one_mul, hunit] using hGNS 1 1

theorem gns_selfadjoint_moments (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (F : A) (hF : star F = F) :
    ⟪J 1, J F⟫_ℂ = ω F ∧
      ⟪J F, J 1⟫_ℂ = ω F ∧
      ⟪J F, J F⟫_ℂ = ω (F * F) ∧ (ω F).im = 0 := by
  have hleft : ⟪J 1, J F⟫_ℂ = ω F := by simpa using hGNS 1 F
  have hright : ⟪J F, J 1⟫_ℂ = ω F := by simpa [hF] using hGNS F 1
  have hsquare : ⟪J F, J F⟫_ℂ = ω (F*F) := by simpa [hF] using hGNS F F
  refine ⟨hleft, hright, hsquare, ?_⟩
  have hc : conj (ω F) = ω F := by
    calc
      conj (ω F) = conj ⟪J 1, J F⟫_ℂ := congrArg conj hleft.symm
      _ = ⟪J F, J 1⟫_ℂ := inner_conj_symm _ _
      _ = ω F := hright
  have him := congrArg Complex.im hc
  simp only [Complex.conj_im] at him
  linarith

/-- Centered variance is derived from the state/inner-product dictionary;
it is not supplied as a separate premise. -/
theorem gns_centered_variance (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1)
    (F : A) (hF : star F = F) :
    let v := J F - ((ω F).re : ℂ) • J 1
    ⟪J 1, v⟫_ℂ = 0 ∧
      ‖v‖^2 = (ω (F*F)).re - (ω F).re^2 := by
  dsimp only
  obtain ⟨hleft, hright, hsquare, him⟩ := gns_selfadjoint_moments ω J hGNS F hF
  have hnorm := gns_unit_inner ω J hGNS hunit
  have hreal : ω F = ((ω F).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him
  constructor
  · rw [inner_sub_right, inner_smul_right, hleft, hnorm, hreal]
    simp
  · rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change (⟪J F - ((ω F).re : ℂ) • J 1,
      J F - ((ω F).re : ℂ) • J 1⟫_ℂ).re = (ω (F*F)).re - (ω F).re^2
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hleft, hright, hsquare, hnorm,
      Complex.sub_re, Complex.mul_re, Complex.conj_ofReal,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      him]
    ring

theorem orthogonal_nonzero_not_vacuum_span
    (Ω v : H) (hΩ : ⟪Ω, Ω⟫_ℂ = 1) (horth : ⟪Ω, v⟫_ℂ = 0) (hv : v ≠ 0) :
    v ∉ Submodule.span ℂ ({Ω} : Set H) := by
  intro hmem
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hmem
  have h := congrArg (fun w : H => ⟪Ω, w⟫_ℂ) hz
  simp only [inner_smul_right, hΩ, mul_one, horth] at h
  apply hv
  rw [← hz, h, zero_smul]

/-- Every GNS realization of the same normalized state has an explicit
nonzero vacuum-orthogonal vector when its real observable has positive variance. -/
theorem gns_nontrivial_of_positive_variance
    (ω : A →ₗ[ℂ] ℂ) (J : A →ₗ[ℂ] H)
    (hGNS : GNSPairing ω J) (hunit : ω 1 = 1)
    (F : A) (hF : star F = F) {c : ℝ} (hc : 0 < c)
    (hvar : c ≤ (ω (F*F)).re - (ω F).re^2) :
    ∃ v : H, ⟪J 1, v⟫_ℂ = 0 ∧ c ≤ ‖v‖^2 ∧ v ≠ 0 ∧
      v ∉ Submodule.span ℂ ({J 1} : Set H) := by
  let v := J F - ((ω F).re : ℂ) • J 1
  obtain ⟨ho, hn⟩ := gns_centered_variance ω J hGNS hunit F hF
  have hb : c ≤ ‖v‖^2 := by simpa only [v, hn] using hvar
  have hv : v ≠ 0 := by
    intro hz
    have : c ≤ 0 := by simpa [hz] using hb
    linarith
  exact ⟨v, ho, hb, hv,
    orthogonal_nonzero_not_vacuum_span (J 1) v
      (gns_unit_inner ω J hGNS hunit) ho hv⟩

#print axioms gns_centered_variance
#print axioms gns_nontrivial_of_positive_variance
end YMUIC.ConditionalI7
