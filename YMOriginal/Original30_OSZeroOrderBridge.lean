import YMOriginal.Original30_AllVolumeJointSchwartz
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03
open Set

/-!
The zero-derivative part of the radial OS (1975), formula (2.1), weight
is enough to pay the existing all-volume bare source estimate.  No bound on
higher derivatives or norm conversion constants is needed.  The parameter M
must be instantiated from the published norm on the actual test function.
This does not prove a renormalized source estimate or a continuum limit.
-/

/-- Zeroth-order part of the radial OS norm at index `8*r`. -/
def osRadialZeroNorm (r : ℕ) (f : YMUIC.Original34.JointTest r) : ℝ :=
  sSup (Set.range fun x : EuclideanSpace ℝ (Fin (4 * r)) =>
    (1 + ‖x‖ ^ 2) ^ (4 * r) * ‖f x‖)

theorem os_radial_zero_bdd (r : ℕ) (f : YMUIC.Original34.JointTest r) :
    BddAbove (Set.range fun x : EuclideanSpace ℝ (Fin (4 * r)) =>
      (1 + ‖x‖ ^ 2) ^ (4 * r) * ‖f x‖) := by
  let P := SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f
  refine ⟨2 ^ (4 * r) * P, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hpow : (1 + ‖x‖ ^ 2) ^ (4 * r) ≤
      2 ^ (4 * r) * (1 + ‖x‖ ^ (8 * r)) := by
    have ha := add_pow_le (a := (1 : ℝ)) (b := ‖x‖ ^ 2)
      (by positivity) (sq_nonneg ‖x‖) (4 * r)
    have hb : (2 : ℝ) ^ (4 * r - 1) ≤ 2 ^ (4 * r) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hc : (1 : ℝ) + (‖x‖ ^ 2) ^ (4 * r) = 1 + ‖x‖ ^ (8 * r) := by
      simp only [← pow_mul, show 2 * (4 * r) = 8 * r by omega]
    rw [one_pow, hc] at ha
    exact ha.trans (mul_le_mul_of_nonneg_right hb (by positivity))
  have hp0 := f.norm_le_seminorm ℂ x
  have hp8 := f.norm_pow_mul_le_seminorm ℂ (8 * r) x
  have hs : (1 + ‖x‖ ^ (8 * r)) * ‖f x‖ ≤ P := by
    dsimp [P]
    nlinarith
  calc
    _ ≤ (2 ^ (4 * r) * (1 + ‖x‖ ^ (8 * r))) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = (2 : ℝ) ^ (4 * r) * ((1 + ‖x‖ ^ (8 * r)) * ‖f x‖) := by ring
    _ ≤ (2 : ℝ) ^ (4 * r) * P := mul_le_mul_of_nonneg_left hs (by positivity)

theorem os_radial_zero_nonneg (r : ℕ) (f : YMUIC.Original34.JointTest r) :
    0 ≤ osRadialZeroNorm r f := by
  have hx := le_csSup (os_radial_zero_bdd r f)
    (Set.mem_range_self (0 : EuclideanSpace ℝ (Fin (4 * r))))
  have hnon : 0 ≤ (1 + ‖(0 : EuclideanSpace ℝ (Fin (4 * r)))‖ ^ 2) ^ (4 * r) *
      ‖f 0‖ := by positivity
  exact hnon.trans hx

theorem os_radial_zero_dominates (r : ℕ) (f : YMUIC.Original34.JointTest r)
    (x : EuclideanSpace ℝ (Fin (4 * r))) :
    (1 + ‖x‖ ^ 2) ^ (4 * r) * ‖f x‖ ≤ osRadialZeroNorm r f :=
  le_csSup (os_radial_zero_bdd r f) (Set.mem_range_self x)

theorem radial_zero_order_controls_schwartz
    (r : ℕ) (f : YMUIC.Original34.JointTest r) (M : ℝ) (hM : 0 ≤ M)
    (hweight : ∀ x : EuclideanSpace ℝ (Fin (4 * r)),
      (1 + ‖x‖ ^ 2) ^ (4 * r) * ‖f x‖ ≤ M) :
    SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f ≤ 2 * M := by
  have h0 : SchwartzMap.seminorm ℂ 0 0 f ≤ M := by
    apply SchwartzMap.seminorm_le_bound ℂ 0 0 f hM
    intro x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
    have hx : 1 ≤ (1 + ‖x‖ ^ 2) ^ (4 * r) := by
      exact one_le_pow₀ (by nlinarith [sq_nonneg ‖x‖])
    calc
      ‖f x‖ = 1 * ‖f x‖ := by ring
      _ ≤ (1 + ‖x‖ ^ 2) ^ (4 * r) * ‖f x‖ :=
        mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ ≤ M := hweight x
  have hw : SchwartzMap.seminorm ℂ (8 * r) 0 f ≤ M := by
    apply SchwartzMap.seminorm_le_bound ℂ (8 * r) 0 f hM
    intro x
    simp only [norm_iteratedFDeriv_zero]
    have hx : ‖x‖ ^ (8 * r) ≤ (1 + ‖x‖ ^ 2) ^ (4 * r) := by
      have hp : (‖x‖ ^ 2) ^ (4 * r) ≤ (1 + ‖x‖ ^ 2) ^ (4 * r) :=
        pow_le_pow_left₀ (sq_nonneg _) (by linarith) (4 * r)
      simpa only [← pow_mul, show 2 * (4 * r) = 8 * r by omega] using hp
    exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans (hweight x)
  linarith

theorem bare_joint_os_zero_weight_bound
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : MeasureTheory.Measure Config) [MeasureTheory.IsProbabilityMeasure μ]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r)
    (hMeas : MeasureTheory.AEStronglyMeasurable
      (fun ω => actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f) μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hweight : ∀ x : EuclideanSpace ℝ (Fin (4 * r)),
      (1 + ‖x‖ ^ 2) ^ (4 * r) * ‖f x‖ ≤ M) :
    MeasureTheory.Integrable
      (fun ω => actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f) μ ∧
    ‖∫ ω, actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
      (U ω) words coeff (actualJointLatticePosition a) f ∂μ‖ ≤
      (2 * Real.exp (24576 * K)) * (r.factorial : ℝ) * M := by
  obtain ⟨hint, hbound⟩ := actual_word_joint_probability_all_volume
    μ r N a ha ha1 U words coeff K hK hbudget f hMeas
  refine ⟨hint, ?_⟩
  have hsum := radial_zero_order_controls_schwartz r f M hM hweight
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have he : (24576 * K) ^ r ≤ Real.exp (24576 * K) * (r.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (24576 * K) (by positivity) r
    exact (div_le_iff₀ hf).mp h
  calc
    _ ≤ (24576 * K) ^ r *
      (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (8 * r) 0 f) := hbound
    _ ≤ (24576 * K) ^ r * (2 * M) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (Real.exp (24576 * K) * (r.factorial : ℝ)) * (2 * M) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by ring

theorem bare_joint_os_radial_zero_bound
    {Config W T : Type*} [MeasurableSpace Config] [Fintype T]
    (μ : MeasureTheory.Measure Config) [MeasureTheory.IsProbabilityMeasure μ]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : Config → TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r)
    (hMeas : MeasureTheory.AEStronglyMeasurable
      (fun ω => actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f) μ) :
    MeasureTheory.Integrable
      (fun ω => actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
        (U ω) words coeff (actualJointLatticePosition a) f) μ ∧
    ‖∫ ω, actualWordJointCutoff r (fun _ => ((a ^ 4 : ℝ) : ℂ))
      (U ω) words coeff (actualJointLatticePosition a) f ∂μ‖ ≤
      (2 * Real.exp (24576 * K)) * (r.factorial : ℝ) * osRadialZeroNorm r f :=
  bare_joint_os_zero_weight_bound μ r N a ha ha1 U words coeff K hK hbudget f hMeas
    (osRadialZeroNorm r f) (os_radial_zero_nonneg r f) (os_radial_zero_dominates r f)

#print axioms radial_zero_order_controls_schwartz
#print axioms bare_joint_os_zero_weight_bound
#print axioms bare_joint_os_radial_zero_bound
end YMUIC.Original30
