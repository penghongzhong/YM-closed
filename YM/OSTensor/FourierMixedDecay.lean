import YM.OSTensor.FourierMixedIdentity
import YM.OSTensor.FourierMultivariateBound

set_option autoImplicit false
namespace YMUIC.OSTensor
open UnitAddTorus

/-- Full mixed Fourier decay, including every zero-frequency coordinate. -/
theorem fourier_mixed_decay {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ j < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i j (i.insertNth (y : UnitAddCircle) z))
        (G i (j + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (k : Fin (n + 1) → ℤ) :
    ‖mFourierCoeff (F 0) k‖ * (∏ i, (1 + |(k i : ℝ)|) ^ 4) ≤
      (4 : ℝ) ^ (n + 1) * ‖F (n + 1)‖ := by
  have hw (i : Fin (n + 1)) : (1 + |(k i : ℝ)|) ^ 4 ≤
      4 * (1 + (2 * Real.pi * (k i : ℝ)) ^ 2) ^ 2 := by
    have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
    have hk := mul_le_mul_of_nonneg_right hp (sq_nonneg (k i : ℝ))
    have h : (1 + |(k i : ℝ)|) ^ 2 ≤ 2 * (1 + (2 * Real.pi * (k i : ℝ)) ^ 2) := by
      nlinarith [sq_nonneg (|(k i : ℝ)| - 1), sq_abs (k i : ℝ)]
    have := pow_le_pow_left₀ (sq_nonneg (1 + |(k i : ℝ)|)) h 2
    nlinarith
  have hprod := Finset.prod_le_prod₀
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      (by positivity : 0 ≤ (1 + |(k i : ℝ)|) ^ 4)) (fun i _ => hw i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hi := congrArg norm (fourier_mixed_identity F G hbase hnext hd k)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => sq_nonneg _))] at hi
  have hb := fourier_multivariate_bound (F (n + 1)) k
  calc
    _ ≤ ‖mFourierCoeff (F 0) k‖ *
        ((4 : ℝ) ^ (n + 1) * ∏ i, (1 + (2 * Real.pi * (k i : ℝ)) ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (4 : ℝ) ^ (n + 1) * ‖mFourierCoeff (F (n + 1)) k‖ := by rw [hi]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
end YMUIC.OSTensor
