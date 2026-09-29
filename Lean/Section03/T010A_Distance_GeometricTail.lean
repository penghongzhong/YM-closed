import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010A

theorem support_recurrence_iterated
    (L b : ℝ) (r : ℕ → ℝ)
    (j : ℕ)
    (hL : 0 < L)
    (hrec : ∀ n, r (n+1) ≥ L⁻¹ * r n - b) :
    r j ≥ L ^ (-(j : ℤ)) * r 0
      - b * (Finset.range j).sum (fun m => L ^ (-(m : ℤ))) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hj := hrec j
      calc
        r (j+1) ≥ L⁻¹ * r j - b := hj
        _ ≥ L⁻¹ *
              (L ^ (-(j : ℤ)) * r 0
                - b * (Finset.range j).sum (fun m => L ^ (-(m : ℤ)))) - b := by
              gcongr
              exact inv_nonneg.mpr hL.le
        _ = L ^ (-((j+1 : ℕ) : ℤ)) * r 0
              - b * (Finset.range (j+1)).sum (fun m => L ^ (-(m : ℤ))) := by
              rw [Finset.sum_range_succ]
              field_simp [ne_of_gt hL]
              ring

theorem distance_lower_bound_from_tail
    (L b : ℝ) (r : ℕ → ℝ)
    (K j : ℕ)
    (hL : 0 < L)
    (hrec : ∀ n, r (n+1) ≥ L⁻¹ * r n - b)
    (htail :
      b * (Finset.range j).sum (fun m => L ^ (-(m : ℤ)))
        ≤ b * L / (L - 1))
    (hpow :
      L ^ (-(j : ℤ)) * r 0 =
        L ^ ((K : ℤ) - (j : ℤ)) *
          (L ^ (-(K : ℤ)) * r 0)) :
    r j ≥
      L ^ ((K : ℤ) - (j : ℤ)) *
        (L ^ (-(K : ℤ)) * r 0)
      - b * L / (L - 1) := by
  have hi := support_recurrence_iterated L b r j hL hrec
  rw [hpow] at hi
  linarith

#print axioms support_recurrence_iterated
#print axioms distance_lower_bound_from_tail

end YMUICV128.Section03.T010A
