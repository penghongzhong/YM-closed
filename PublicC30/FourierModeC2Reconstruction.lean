import PublicC30.FourierModeC2TsumDerivative

set_option autoImplicit false
namespace YMUIC.OSTensor
open UnitAddTorus

/-- The existing mixed fourth-order coefficient theorem implies ordinary
absolute Fourier summability, with no extra model hypothesis. -/
theorem fourier_mixed_coefficient_summable {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ t < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i t (i.insertNth (y : UnitAddCircle) z))
        (G i (t + 1) (i.insertNth (x : UnitAddCircle) z)) x) :
    Summable (mFourierCoeff (F 0)) := by
  have hs := (fourier_mixed_c2_summability F G hbase hnext hd).1
  have hone (k : Fin (n + 1) → ℤ) :
      (1 : ℝ) ≤ ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2 := by
    have h := Finset.prod_le_prod₀
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun _ => (1 : ℝ))
      (g := fun t => (1 + |(k t : ℝ)|) ^ 2)
      (fun _ _ => by norm_num)
      (fun t _ => by nlinarith [abs_nonneg (k t : ℝ)])
    simpa only [Finset.prod_const_one] using h
  have hn : Summable (fun k : Fin (n + 1) → ℤ => ‖mFourierCoeff (F 0) k‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      calc
        _ = ‖mFourierCoeff (F 0) k‖ * 1 := by ring
        _ ≤ ‖mFourierCoeff (F 0) k‖ *
            ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2 :=
          mul_le_mul_of_nonneg_left (hone k) (norm_nonneg _))
  exact hn.of_norm

/-- For the actual C^4 periodic input, the absolutely convergent Fourier
series reconstructs the *true* first coordinate derivative, not only a formal
coefficient series. -/
theorem fourier_mixed_c2_first_derivative {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ t < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i t (i.insertNth (y : UnitAddCircle) z))
        (G i (t + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (i : Fin (n + 1)) (z : UnitAddTorus (Fin n)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => F 0 (i.insertNth (y : UnitAddCircle) z))
      (∑' k : Fin (n + 1) → ℤ,
        mFourierCoeff (F 0) k *
          ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) *
            mFourier k (i.insertNth (x : UnitAddCircle) z))) x := by
  have hc := fourier_mixed_coefficient_summable F G hbase hnext hd
  have he (y : ℝ) :
      (∑' k : Fin (n + 1) → ℤ,
        mFourierCoeff (F 0) k * mFourier k (i.insertNth (y : UnitAddCircle) z)) =
        F 0 (i.insertNth (y : UnitAddCircle) z) := by
    simpa only [smul_eq_mul] using
      (hasSum_mFourier_series_apply_of_summable hc
        (i.insertNth (y : UnitAddCircle) z)).tsum_eq
  have hfun : (fun y : ℝ => ∑' k : Fin (n + 1) → ℤ,
      mFourierCoeff (F 0) k * mFourier k (i.insertNth (y : UnitAddCircle) z)) =
        (fun y : ℝ => F 0 (i.insertNth (y : UnitAddCircle) z)) := funext he
  have h := fourier_mixed_series_real_derivative F G hbase hnext hd i z 0
    (by norm_num) x
  simpa only [pow_zero, one_mul, zero_add, pow_one, hfun] using h

/-- The same normalized coefficient data reconstruct the next coordinate
derivative, completing the genuine two-derivative Fourier series passage. -/
theorem fourier_mixed_c2_second_derivative {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ t < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i t (i.insertNth (y : UnitAddCircle) z))
        (G i (t + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (i : Fin (n + 1)) (z : UnitAddTorus (Fin n)) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∑' k : Fin (n + 1) → ℤ,
        mFourierCoeff (F 0) k *
          ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) *
            mFourier k (i.insertNth (y : UnitAddCircle) z)))
      (∑' k : Fin (n + 1) → ℤ,
        mFourierCoeff (F 0) k *
          ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ 2 *
            mFourier k (i.insertNth (x : UnitAddCircle) z))) x := by
  simpa only [pow_one, Nat.reduceAdd] using
    (fourier_mixed_series_real_derivative F G hbase hnext hd i z 1
      (by norm_num) x)

end YMUIC.OSTensor
