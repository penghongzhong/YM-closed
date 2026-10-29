import PublicC30.FourierModeC2Growth
import YM.OSTensor.FourierMixedC2Summability

set_option autoImplicit false
namespace YMUIC.OSTensor
open UnitAddTorus

/-- Every mixed partial derivative with at most two derivatives in each real
coordinate is bounded by one joint Fourier frequency weight, with no factorial
loss in the number of four-dimensional blocks. -/
theorem fourier_mode_coordinate_frequency_product_bound {n : ℕ}
    (k : Fin (n + 1) → ℤ) (β : Fin (n + 1) → ℕ)
    (hβ : ∀ i, β i ≤ 2) :
    ‖∏ i : Fin (n + 1),
        (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ β i‖ ≤
      ((2 * Real.pi) ^ 2) ^ (n + 1) *
        ∏ i : Fin (n + 1), (1 + |(k i : ℝ)|) ^ 2 := by
  have hi (i : Fin (n + 1)) :
      ‖(2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ β i‖ ≤
        (2 * Real.pi) ^ 2 * (1 + |(k i : ℝ)|) ^ 2 := by
    have h := fourier_mode_coordinate_c2_bound k i
      (fun _ : Fin n => (0 : UnitAddCircle)) (β i) (hβ i) 0
    rw [fourier_mode_coordinate_iterated_norm] at h
    simpa only [norm_pow] using h
  rw [norm_prod]
  calc
    (∏ i : Fin (n + 1),
      ‖(2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ β i‖) ≤
      ∏ i : Fin (n + 1),
        ((2 * Real.pi) ^ 2 * (1 + |(k i : ℝ)|) ^ 2) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hi i)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

/-- Actual joint Fourier fourth-derivative control implies summability of
the complete family of C² derivative multipliers for every multiindex β≤2. -/
theorem fourier_mode_c2_coefficient_summable {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ j < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i j (i.insertNth (y : UnitAddCircle) z))
        (G i (j + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (β : Fin (n + 1) → ℕ) (hβ : ∀ i, β i ≤ 2) :
    Summable (fun k : Fin (n + 1) → ℤ =>
      ‖mFourierCoeff (F 0) k‖ *
        ‖∏ i : Fin (n + 1),
          (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ β i‖) := by
  let C : ℝ := ((2 * Real.pi) ^ 2) ^ (n + 1)
  have hs := (fourier_mixed_c2_summability F G hbase hnext hd).1
  have hsC := hs.mul_left C
  apply hsC.of_nonneg_of_le
  · intro k
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro k
    calc
      _ ≤ ‖mFourierCoeff (F 0) k‖ *
          (C * ∏ i : Fin (n + 1), (1 + |(k i : ℝ)|) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (fourier_mode_coordinate_frequency_product_bound k β hβ) (norm_nonneg _)
      _ = C * (‖mFourierCoeff (F 0) k‖ *
          ∏ i : Fin (n + 1), (1 + |(k i : ℝ)|) ^ 2) := by ring

/-- The C² Fourier jets converge absolutely as Banach-valued series, not
merely as an assumed pointwise scalar coefficient sum. -/
theorem fourier_mode_c2_jet_summable {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ j < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i j (i.insertNth (y : UnitAddCircle) z))
        (G i (j + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (β : Fin (n + 1) → ℕ) (hβ : ∀ i, β i ≤ 2) :
    Summable (fun k : Fin (n + 1) → ℤ =>
      (mFourierCoeff (F 0) k *
        ∏ i : Fin (n + 1),
          (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ β i) • mFourier k) := by
  have hs := fourier_mode_c2_coefficient_summable F G hbase hnext hd β hβ
  apply Summable.of_norm
  simpa only [norm_smul, norm_mul, mFourier_norm, mul_one] using hs

end YMUIC.OSTensor
