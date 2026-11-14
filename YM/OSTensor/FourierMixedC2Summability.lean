import YM.OSTensor.FourierMixedDecay
import YM.OSTensor.FourierQuadraticWeight
import YM.OSTensor.ProductSeries

set_option autoImplicit false
namespace YMUIC.OSTensor
open UnitAddTorus

/-- Actual mixed periodic derivatives yield the joint second-order Fourier
budget with an exponential dimension constant and no assumed coefficient bound. -/
theorem fourier_mixed_c2_summability {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ j < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i j (i.insertNth (y : UnitAddCircle) z))
        (G i (j + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    : Summable (fun k : Fin (n + 1) → ℤ =>
        ‖mFourierCoeff (F 0) k‖ * ∏ i, (1 + |(k i : ℝ)|) ^ 2) ∧
      (∑' k : Fin (n + 1) → ℤ, ‖mFourierCoeff (F 0) k‖ * ∏ i, (1 + |(k i : ℝ)|) ^ 2) ≤
        (4 * ∑' k : ℤ, 1 / (1 + |(k : ℝ)|) ^ 2) ^ (n + 1) * ‖F (n + 1)‖ := by
  let B := (4 : ℝ) ^ (n + 1) * ‖F (n + 1)‖
  have hs := product_series (n + 1)
    (fun _ (k : ℤ) => 1 / (1 + |(k : ℝ)|) ^ 2)
    (fun _ _ => by positivity) (fun _ => fourier_quadratic_weight)
  have hb (k : Fin (n + 1) → ℤ) :
      ‖mFourierCoeff (F 0) k‖ * ∏ i, (1 + |(k i : ℝ)|) ^ 2 ≤
        B * ∏ i, 1 / (1 + |(k i : ℝ)|) ^ 2 := by
    have hpos : 0 < ∏ i, (1 + |(k i : ℝ)|) ^ 2 := Finset.prod_pos (fun i _ => by positivity)
    rw [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
    apply (le_div_iff₀ hpos).mpr
    have he : (∏ i, (1 + |(k i : ℝ)|) ^ 2) * (∏ i, (1 + |(k i : ℝ)|) ^ 2) =
        ∏ i, (1 + |(k i : ℝ)|) ^ 4 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [mul_assoc, he]
    exact fourier_mixed_decay F G hbase hnext hd k
  have hsB := hs.summable.mul_left B
  have hn := hsB.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg (fun i _ => by positivity))) hb
  refine ⟨hn, (hn.tsum_le_tsum hb hsB).trans_eq ?_⟩
  rw [tsum_mul_left, hs.tsum_eq]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  dsimp [B]
  rw [mul_pow]
  ring
end YMUIC.OSTensor
