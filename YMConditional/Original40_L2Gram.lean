import YMConditional.Original41_MomentLimit
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section
namespace YMUIC.ConditionalI7
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate

variable {X : Type*} [MeasurableSpace X]

/-- The same real observable is centered before entering the complex L2 space. -/
def centeredFunction (μ : Measure X) (F : X → ℝ) : X → ℂ :=
  fun x => ((F x - ∫ y, F y ∂μ : ℝ) : ℂ)

theorem centeredFunction_memLp (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ) : MemLp (centeredFunction μ F) 2 μ := by
  exact Complex.ofRealCLM.comp_memLp' (hF.sub (memLp_const (∫ y, F y ∂μ)))

/-- Genuine almost-everywhere equivalence class, not a free Hilbert vector. -/
def centeredVector (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ) : Lp ℂ 2 μ :=
  (centeredFunction_memLp μ F hF).toLp (centeredFunction μ F)

def vacuumVector (μ : Measure X) [IsProbabilityMeasure μ] : Lp ℂ 2 μ :=
  (memLp_const (1 : ℂ)).toLp (fun _ : X => (1 : ℂ))

theorem centeredVector_coe (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ) :
    centeredVector μ F hF =ᵐ[μ] centeredFunction μ F :=
  MemLp.coeFn_toLp _

/-- The Gram/variance dictionary is proved from the actual L2 inner product. -/
theorem centeredVector_norm_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ) :
    ‖centeredVector μ F hF‖^2 = cutoffVariance μ F := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner _ _)]
  unfold cutoffVariance
  apply integral_congr_ae
  filter_upwards [centeredVector_coe μ F hF] with x hx
  rw [hx]
  simp [centeredFunction, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two]

theorem centeredVector_orthogonal_vacuum (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ) :
    ⟪vacuumVector μ, centeredVector μ F hF⟫_ℂ = 0 := by
  rw [L2.inner_def]
  have heq : (∫ x, ⟪vacuumVector μ x, centeredVector μ F hF x⟫_ℂ ∂μ) =
      ∫ x, ((F x - ∫ y, F y ∂μ : ℝ) : ℂ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := μ)),
      centeredVector_coe μ F hF] with x h1 hx
    change vacuumVector μ x = 1 at h1
    rw [h1, hx]
    simp [centeredFunction, RCLike.inner_apply]
  rw [heq, integral_complex_ofReal,
    integral_sub (hF.integrable (by norm_num)) (integrable_const _)]
  simp

/-- Gram deficit at the original positive bounded physical transfer. -/
def transferDeficit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (v : H) : ℝ := ‖v‖^2 - (⟪v, T v⟫_ℂ).re

theorem transferDeficit_le_norm_sq {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : T.IsPositive) (v : H) :
    transferDeficit T v ≤ ‖v‖^2 := by
  have hnonneg : 0 ≤ (⟪v, T v⟫_ℂ).re :=
    (Complex.le_def.mp (hT.inner_nonneg_right v)).1
  exact sub_le_self _ hnonneg

/-- Applies to a physical realization as well as directly to complex L2.
No variance/norm equality is an assumption. -/
theorem physical_deficit_le_variance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : MemLp F 2 μ)
    (J : Lp ℂ 2 μ →ₗᵢ[ℂ] H)
    (T : H →L[ℂ] H) (hT : T.IsPositive) :
    transferDeficit T (J (centeredVector μ F hF)) ≤ cutoffVariance μ F := by
  calc
    transferDeficit T (J (centeredVector μ F hF))
      ≤ ‖J (centeredVector μ F hF)‖^2 := transferDeficit_le_norm_sq T hT _
    _ = cutoffVariance μ F := by rw [J.norm_map, centeredVector_norm_sq]

end YMUIC.ConditionalI7
