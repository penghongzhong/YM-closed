import PublicC30.ScaledShellExponentBudget

set_option autoImplicit false

namespace YMUIC.OSTensor

/--
The exact positive-real power version of the maximum-shell exponent budget.
It preserves the uniform factor 2^((d+17)r) and the decay (d+1)r.
-/
theorem scaled_shell_power_budget {r d : ℕ} (n : Fin r → ℕ) :
    (2 : ℝ) ^ (16 * (∑ j : Fin r, n j)) *
        (2 : ℝ) ^ ((d + 1) * r * Finset.univ.sup n) ≤
      (2 : ℝ) ^ ((d + 17) * r * (Finset.univ.sup n - 1)) *
        (2 : ℝ) ^ ((d + 17) * r) := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (scaled_shell_exponent_budget (r := r) (d := d) n)
  simpa only [pow_add] using h

end YMUIC.OSTensor
