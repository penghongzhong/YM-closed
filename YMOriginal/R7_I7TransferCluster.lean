import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

set_option autoImplicit false
noncomputable section

namespace YMUIC.R7

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Iteration of the physical transfer map on vectors, written recursively
so the clustering certificate does not depend on any spectral API. -/
def transferIterate (T : H →L[ℂ] H) : ℕ → H → H
  | 0, x => x
  | n + 1, x => T (transferIterate T n x)

/-- A one-step vacuum-orthogonal contraction iterates with q^n. -/
theorem transferIterate_norm_le
    (T : H →L[ℂ] H) (q : ℝ)
    (hq : 0 ≤ q)
    (hT : ∀ x : H, ‖T x‖ ≤ q * ‖x‖) :
    ∀ n x, ‖transferIterate T n x‖ ≤ q ^ n * ‖x‖ := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [transferIterate]
  | succ n ih =>
      intro x
      rw [transferIterate]
      calc
        ‖T (transferIterate T n x)‖
            ≤ q * ‖transferIterate T n x‖ := hT _
        _ ≤ q * (q ^ n * ‖x‖) :=
          mul_le_mul_of_nonneg_left (ih x) hq
        _ = q ^ (n + 1) * ‖x‖ := by
          rw [pow_succ]
          ring

/-- R7 I7-to-cluster core: transfer contraction gives exponential
decay of centered Hilbert-space pairings. The centering/vacuum
orthogonality is supplied by the caller; no RG-distance premise occurs. -/
theorem transfer_contraction_pairing_le
    (T : H →L[ℂ] H) (q : ℝ)
    (hq : 0 ≤ q)
    (hT : ∀ x : H, ‖T x‖ ≤ q * ‖x‖)
    (n : ℕ) (x y : H) :
    ‖@inner ℂ H _ x (transferIterate T n y)‖
      ≤ q ^ n * ‖x‖ * ‖y‖ := by
  have hinner :=
    norm_inner_le_norm x (transferIterate T n y)
  have hit := transferIterate_norm_le T q hq hT n y
  calc
    ‖@inner ℂ H _ x (transferIterate T n y)‖
        ≤ ‖x‖ * ‖transferIterate T n y‖ := hinner
    _ ≤ ‖x‖ * (q ^ n * ‖y‖) :=
      mul_le_mul_of_nonneg_left hit (norm_nonneg x)
    _ = q ^ n * ‖x‖ * ‖y‖ := by ring

#print axioms transferIterate_norm_le
#print axioms transfer_contraction_pairing_le

end YMUIC.R7
