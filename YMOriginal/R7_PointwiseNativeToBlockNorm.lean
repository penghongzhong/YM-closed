import YMOriginal.Original24_NativeShellU1

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-- R7 bridge: a pointwise native exponential activity bound plus the
already verified physical shell count gives the weighted per-block norm.
No total block-norm hypothesis is assumed. -/
theorem r7_pointwise_native_to_block_norm
    {Γ Block : Type*} [Fintype Γ] [DecidableEq Block]
    (support : Γ → Finset Block) (d : Γ → ℕ)
    (z : Γ → ℂ)
    (amp Cpol cpol kappaR kappa : ℝ)
    (hamp : 0 ≤ amp) (hCpol : 0 ≤ Cpol)
    (hgap : 0 < kappaR - kappa - cpol)
    (hz : ∀ X, ‖z X‖ ≤
      amp * Real.exp (-kappaR * (d X : ℝ)))
    (hShell : ∀ Delta : Block, ∀ m : ℕ,
      ((actualThroughBlock support Delta).filter
        (fun X => d X = m)).card ≤
        Cpol * Real.exp (cpol * (m : ℝ))) :
    ∀ Delta : Block,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤
      amp * (Cpol /
        (1 - Real.exp (-(kappaR - kappa - cpol)))) := by
  intro Delta
  have hshell :=
    actual_native_U1_shell_count_to_block_norm
      support d Cpol cpol kappaR kappa hCpol hgap hShell Delta
  have hterm (X : Γ) :
      ‖z X‖ * Real.exp (kappa * (d X : ℝ)) ≤
        amp * Real.exp (-(kappaR - kappa) * (d X : ℝ)) := by
    calc
      ‖z X‖ * Real.exp (kappa * (d X : ℝ))
          ≤ (amp * Real.exp (-kappaR * (d X : ℝ))) *
              Real.exp (kappa * (d X : ℝ)) :=
        mul_le_mul_of_nonneg_right (hz X) (Real.exp_pos _).le
      _ = amp * Real.exp (-(kappaR - kappa) * (d X : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  calc
    (∑ X ∈ actualThroughBlock support Delta,
      ‖z X‖ * Real.exp (kappa * (d X : ℝ)))
        ≤ ∑ X ∈ actualThroughBlock support Delta,
            amp * Real.exp (-(kappaR - kappa) * (d X : ℝ)) :=
      Finset.sum_le_sum (fun X hX => hterm X)
    _ = amp * (∑ X ∈ actualThroughBlock support Delta,
          Real.exp (-(kappaR - kappa) * (d X : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ amp * (Cpol /
          (1 - Real.exp (-(kappaR - kappa - cpol)))) :=
      mul_le_mul_of_nonneg_left hshell hamp

#print axioms r7_pointwise_native_to_block_norm

end YMUIC.Original24
