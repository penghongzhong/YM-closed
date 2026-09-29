import Mathlib
import Section03.T010A_Distance_GeometricTail
import Section03.T010B_Supergeom

set_option autoImplicit false

namespace YMUICV128.Section03.T010C

theorem reverse_scale_sum (f : ℕ → ℝ) (K : ℕ) :
    (Finset.range K).sum (fun j => f (K - j)) =
      (Finset.range K).sum (fun n => f (n + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ']
      have hs : (Finset.range K).sum (fun j => f (K + 1 - (j + 1))) =
          (Finset.range K).sum (fun j => f (K - j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        omega
      rw [hs, ih, Finset.sum_range_succ]
      simp

theorem uv_shell_sum_bound (L mu R Binf Cstar : ℝ) (K : ℕ)
    (cov r : ℕ → ℝ) (hL : 2 ≤ L) (hmu : 0 < mu) (hR : 0 < R)
    (hC : 0 ≤ Cstar)
    (hshell : ∀ j < K, |cov j| ≤ Cstar * Real.exp (-mu * r j))
    (hdist : ∀ j < K, L ^ (K - j) * R - Binf ≤ r j) :
    (Finset.range K).sum (fun j => |cov j|) ≤
      Cstar * Real.exp (mu * Binf) *
        (Real.exp (-mu * L * R) / (1 - Real.exp (-mu * L * R))) := by
  have hfac : 0 ≤ Cstar * Real.exp (mu * Binf) := mul_nonneg hC (Real.exp_pos _).le
  have hpoint (j : ℕ) (hj : j < K) :
      |cov j| ≤ (Cstar * Real.exp (mu * Binf)) * Real.exp (-mu * L ^ (K - j) * R) := by
    have hd := mul_le_mul_of_nonneg_left (hdist j hj) hmu.le
    have he : -mu * r j ≤ mu * Binf + (-mu * L ^ (K - j) * R) := by nlinarith only [hd]
    calc
      |cov j| ≤ Cstar * Real.exp (-mu * r j) := hshell j hj
      _ ≤ Cstar * Real.exp (mu * Binf + (-mu * L ^ (K - j) * R)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC
      _ = _ := by rw [Real.exp_add]; ring
  calc
    (Finset.range K).sum (fun j => |cov j|) ≤
        (Finset.range K).sum (fun j => (Cstar * Real.exp (mu * Binf)) *
          Real.exp (-mu * L ^ (K - j) * R)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hpoint j (Finset.mem_range.mp hj)
    _ = (Cstar * Real.exp (mu * Binf)) *
        (Finset.range K).sum (fun j => Real.exp (-mu * L ^ (K - j) * R)) := by rw [Finset.mul_sum]
    _ = (Cstar * Real.exp (mu * Binf)) *
        (Finset.range K).sum (fun n => Real.exp (-mu * L ^ (n + 1) * R)) := by
          rw [reverse_scale_sum (fun n => Real.exp (-mu * L ^ n * R)) K]
    _ ≤ _ := mul_le_mul_of_nonneg_left (T010B.supergeom_sum_bound L mu R K hL hmu hR) hfac

theorem uv_shell_sum_from_recurrence (L b mu Cstar : ℝ) (K : ℕ)
    (cov r : ℕ → ℝ) (hL : 2 ≤ L) (hb : 0 ≤ b) (hmu : 0 < mu)
    (hR : 0 < L ^ (-(K : ℤ)) * r 0) (hC : 0 ≤ Cstar)
    (hrec : ∀ j < K, L⁻¹ * r j - b ≤ r (j + 1))
    (hshell : ∀ j < K, |cov j| ≤ Cstar * Real.exp (-mu * r j)) :
    (Finset.range K).sum (fun j => |cov j|) ≤
      Cstar * Real.exp (mu * (b * L / (L - 1))) *
        (Real.exp (-mu * L * (L ^ (-(K : ℤ)) * r 0)) /
          (1 - Real.exp (-mu * L * (L ^ (-(K : ℤ)) * r 0)))) := by
  apply uv_shell_sum_bound L mu (L ^ (-(K : ℤ)) * r 0) (b * L / (L - 1)) Cstar K cov r hL hmu hR hC hshell
  intro j hj
  exact T010A.distance_lower_bound L b r K j (by linarith) hb (by omega) hrec

#print axioms reverse_scale_sum
#print axioms uv_shell_sum_bound
#print axioms uv_shell_sum_from_recurrence

end YMUICV128.Section03.T010C
