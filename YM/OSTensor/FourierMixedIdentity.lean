import YM.OSTensor.FourierCoordinateElliptic

set_option autoImplicit false
namespace YMUIC.OSTensor
open UnitAddTorus

/-- Successive coordinate operators give the full product multiplier on an
arbitrary, not necessarily separable, continuous periodic function. -/
theorem fourier_mixed_identity {n : ℕ}
    (F : ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (G : Fin (n + 1) → ℕ → C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hbase : ∀ i, G i 0 = F i.val)
    (hnext : ∀ i, F (i.val + 1) = G i 0 - (2 : ℂ) • G i 2 + G i 4)
    (hd : ∀ i, ∀ j < 4, ∀ z : UnitAddTorus (Fin n), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => G i j (i.insertNth (y : UnitAddCircle) z))
        (G i (j + 1) (i.insertNth (x : UnitAddCircle) z)) x)
    (k : Fin (n + 1) → ℤ) :
    mFourierCoeff (F (n + 1)) k =
      (∏ i, ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2) ^ 2 : ℝ)) * mFourierCoeff (F 0) k := by
  let a : ℕ → ℂ := fun j => if h : j < n + 1 then
    (((1 + (2 * Real.pi * (k ⟨j, h⟩ : ℝ)) ^ 2) ^ 2 : ℝ) : ℂ) else 1
  have hs (j : ℕ) (h : j ≤ n + 1) : mFourierCoeff (F j) k =
      (∏ l ∈ Finset.range j, a l) * mFourierCoeff (F 0) k := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj : j < n + 1 := by omega
      have he := fourier_coordinate_elliptic (⟨j, hj⟩ : Fin (n + 1)) (G ⟨j, hj⟩) (hd ⟨j, hj⟩) k
      rw [← hnext, hbase] at he
      rw [he, ih (by omega), Finset.prod_range_succ]
      simp only [a, dite_eq_left hj]
      ring
  rw [hs (n + 1) le_rfl, ← Fin.prod_univ_eq_prod_range]
  simp only [a, dite_eq_left (Fin.isLt _), Complex.ofReal_prod]
end YMUIC.OSTensor
