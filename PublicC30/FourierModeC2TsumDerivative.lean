import PublicC30.FourierModeC2Growth
import YM.OSTensor.FourierMixedC2Summability
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
namespace YMUIC.OSTensor
open UnitAddTorus

/-- A genuinely differentiable Fourier series from a joint quadratic weighted
coefficient budget. This does not assume the derivative of the series exists:
it derives that conclusion from the explicitly constructed Fourier atoms,
their norm bounds and the smooth-series theorem. -/
theorem fourier_c2_weighted_series_hasDerivAt {n : ℕ}
    (c : (Fin (n + 1) → ℤ) → ℂ)
    (hc : Summable (fun k : Fin (n + 1) → ℤ =>
      ‖c k‖ * ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2))
    (i : Fin (n + 1)) (z : UnitAddTorus (Fin n))
    (j : ℕ) (hj : j ≤ 1) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∑' k : Fin (n + 1) → ℤ,
        c k * ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j *
          mFourier k (i.insertNth (y : UnitAddCircle) z)))
      (∑' k : Fin (n + 1) → ℤ,
        c k * ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ (j + 1) *
          mFourier k (i.insertNth (x : UnitAddCircle) z))) x := by
  let C : ℝ := (2 * Real.pi) ^ 2
  let u : (Fin (n + 1) → ℤ) → ℝ := fun k =>
    C * (‖c k‖ * ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2)
  have hu : Summable u := hc.mul_left C
  have hs (k : Fin (n + 1) → ℤ) :
      (1 + |(k i : ℝ)|) ^ 2 ≤
        ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2 := by
    have hw (t : Fin (n + 1)) :
        (1 : ℝ) ≤ (1 + |(k t : ℝ)|) ^ 2 := by
      nlinarith [abs_nonneg (k t : ℝ)]
    calc
      _ = ∏ t : Fin (n + 1),
          (if t = i then (1 + |(k t : ℝ)|) ^ 2 else (1 : ℝ)) := by simp
      _ ≤ ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2 := by
        apply Finset.prod_le_prod₀
        · intro t _
          by_cases ht : t = i <;> simp [ht] <;> positivity
        · intro t _
          by_cases ht : t = i
          · simp [ht]
          · simpa [ht] using hw t
  have hb (k : Fin (n + 1) → ℤ) (m : ℕ) (hm : m ≤ 2) (y : ℝ) :
      ‖c k * ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ m *
        mFourier k (i.insertNth (y : UnitAddCircle) z))‖ ≤ u k := by
    calc
      _ = ‖c k‖ * ‖(2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ m *
          mFourier k (i.insertNth (y : UnitAddCircle) z)‖ := norm_mul _ _
      _ ≤ ‖c k‖ * (C * (1 + |(k i : ℝ)|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (fourier_mode_coordinate_c2_bound k i z m hm y) (norm_nonneg _)
      _ ≤ ‖c k‖ * (C * ∏ t : Fin (n + 1), (1 + |(k t : ℝ)|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hs k) (by positivity)) (norm_nonneg _)
      _ = u k := by dsimp [u, C]; ring
  let g : (Fin (n + 1) → ℤ) → ℝ → ℂ := fun k y =>
    c k * ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j *
      mFourier k (i.insertNth (y : UnitAddCircle) z))
  let gp : (Fin (n + 1) → ℤ) → ℝ → ℂ := fun k y =>
    c k * ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ (j + 1) *
      mFourier k (i.insertNth (y : UnitAddCircle) z))
  have hg (k : Fin (n + 1) → ℤ) (y : ℝ) :
      HasDerivAt (g k) (gp k y) y := by
    dsimp [g, gp]
    exact (fourier_mode_coordinate_iterated_hasDerivAt k i z j y).const_mul (c k)
  have hgp (k : Fin (n + 1) → ℤ) (y : ℝ) :
      ‖gp k y‖ ≤ u k := by
    exact hb k (j + 1) (by omega) y
  have hg0 : Summable (fun k => g k 0) :=
    Summable.of_norm_bounded hu (fun k => hb k j (by omega) 0)
  change HasDerivAt (fun y : ℝ => ∑' k, g k y) (∑' k, gp k x) x
  exact hasDerivAt_tsum hu hg hgp hg0 x

/-- Specialization to the actual joint Fourier coefficients: the derivative
of the Fourier expansion is reconstructed from coefficients of the original
periodic function, assuming only its actual coordinate fourth-derivative chain. -/
theorem fourier_mixed_series_real_derivative {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ t < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i t (i.insertNth (y : UnitAddCircle) z))
        (G i (t + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (i : Fin (n + 1)) (z : UnitAddTorus (Fin n))
    (j : ℕ) (hj : j ≤ 1) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∑' k : Fin (n + 1) → ℤ,
        mFourierCoeff (F 0) k *
          ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ j *
            mFourier k (i.insertNth (y : UnitAddCircle) z)))
      (∑' k : Fin (n + 1) → ℤ,
        mFourierCoeff (F 0) k *
          ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ (j + 1) *
            mFourier k (i.insertNth (x : UnitAddCircle) z))) x := by
  exact fourier_c2_weighted_series_hasDerivAt (mFourierCoeff (F 0))
    (fourier_mixed_c2_summability F G hbase hnext hd).1 i z j hj x

end YMUIC.OSTensor
