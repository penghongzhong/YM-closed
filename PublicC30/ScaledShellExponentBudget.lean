import Mathlib

set_option autoImplicit false

namespace YMUIC.OSTensor

/--
Exact exponent bookkeeping for the maximum-shell Fourier localization.
This theorem is purely arithmetic: it does not assume Wilson source bounds,
periodization, or an OS reconstruction interface.
-/
theorem scaled_shell_exponent_budget {r d : ℕ} (n : Fin r → ℕ) :
    16 * (∑ j : Fin r, n j) + (d + 1) * r * Finset.univ.sup n ≤
      (d + 17) * r * (Finset.univ.sup n - 1) + (d + 17) * r := by
  have hs : (∑ j : Fin r, n j) ≤ r * Finset.univ.sup n := by
    calc
      _ ≤ ∑ _j : Fin r, Finset.univ.sup n :=
        Finset.sum_le_sum (fun j hj => Finset.le_sup hj)
      _ = _ := by simp
  have h16 : 16 * (∑ j : Fin r, n j) ≤
      16 * (r * Finset.univ.sup n) := Nat.mul_le_mul_left 16 hs
  have h0 : 16 * (∑ j : Fin r, n j) +
      (d + 1) * r * Finset.univ.sup n ≤
      (d + 17) * r * Finset.univ.sup n := by
    calc
      _ ≤ 16 * (r * Finset.univ.sup n) +
          (d + 1) * r * Finset.univ.sup n :=
        Nat.add_le_add_right h16 _
      _ = _ := by ring
  have hN : Finset.univ.sup n ≤ (Finset.univ.sup n - 1) + 1 := by omega
  have hm := Nat.mul_le_mul_left ((d + 17) * r) hN
  calc
    _ ≤ (d + 17) * r * Finset.univ.sup n := h0
    _ ≤ (d + 17) * r * ((Finset.univ.sup n - 1) + 1) := hm
    _ = _ := by ring

end YMUIC.OSTensor
