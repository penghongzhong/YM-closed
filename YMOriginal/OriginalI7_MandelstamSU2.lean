import YMOriginal.OriginalI7_MandelstamMatrix
import YM.Wilson.RootBound

set_option autoImplicit false
noncomputable section

namespace YMUIC.I7
open YMUICV128.Section03

/-!
# SU(2) specialization of the exact matrix trace-fusion theorem

The matrix-level identity in the preceding module is already strictly
Lean-certified. This specialization checks the determinant-one fact
that adjugate B is the actual SU(2) inverse B^-1, allowing the
two product terms to be identified with *genuine concatenated holonomies*.

This is only an SU(2) algebraic theorem. No physical I7 or RG estimate
is claimed.
-/

/-- For a determinant-one matrix, the classical adjugate is its group
inverse, specialized to the actual special-unitary-group subtype. -/
theorem su2_matrix_inverse_eq_adjugate (B : SU2) :
    ((B⁻¹ : SU2) : M2) = (B : M2).adjugate := by
  let M : M2 := B
  let N : M2 := (B⁻¹ : SU2)
  have hdet : M.det = 1 := by
    change (B.val).det = 1
    exact (Matrix.mem_specialUnitaryGroup_iff.mp B.property).2
  have hMN : M * N = 1 := by
    change ((B * B⁻¹ : SU2) : M2) = 1
    rw [mul_inv_cancel]
    rfl
  have hJM : M.adjugate * M = 1 := by
    simpa only [hdet, one_smul] using Matrix.adjugate_mul M
  have hN : N = M.adjugate := by
    calc
      N = (1 : M2) * N := by rw [one_mul]
      _ = (M.adjugate * M) * N := by rw [hJM]
      _ = M.adjugate * (M * N) := by rw [mul_assoc]
      _ = M.adjugate := by rw [hMN, mul_one]
  simpa only [N, M] using hN

/-- Actual SU(2) Mandelstam trace identity with true group inverse. -/
theorem su2_mandelstam_trace (A B : SU2) :
    Matrix.trace (A : M2) * Matrix.trace (B : M2) =
      Matrix.trace ((A * B : SU2) : M2) +
        Matrix.trace ((A * B⁻¹ : SU2) : M2) := by
  have h := trace_product_adjugate_fusion (A : M2) (B : M2)
  rw [← su2_matrix_inverse_eq_adjugate B] at h
  change Matrix.trace (A : M2) * Matrix.trace (B : M2) =
    Matrix.trace ((A : M2) * (B : M2)) +
      Matrix.trace ((A : M2) * ((B⁻¹ : SU2) : M2))
  exact h

/-- Exact complex Wilson-root fusion for actual SU(2) holonomies.
Each product on the right is an SU(2) group product and may be
read as a based-loop concatenation. -/
theorem su2_complex_wilson_root_fusion (A B : SU2) :
    complexWilsonRoot (A : M2) * complexWilsonRoot (B : M2) =
      2 * complexWilsonRoot (A : M2) +
        2 * complexWilsonRoot (B : M2) -
        complexWilsonRoot ((A * B : SU2) : M2) -
        complexWilsonRoot ((A * B⁻¹ : SU2) : M2) := by
  have h := complex_wilson_root_fusion (A : M2) (B : M2)
  rw [← su2_matrix_inverse_eq_adjugate B] at h
  change complexWilsonRoot (A : M2) * complexWilsonRoot (B : M2) =
    2 * complexWilsonRoot (A : M2) +
      2 * complexWilsonRoot (B : M2) -
      complexWilsonRoot ((A : M2) * (B : M2)) -
      complexWilsonRoot ((A : M2) * ((B⁻¹ : SU2) : M2))
  exact h

#print axioms su2_matrix_inverse_eq_adjugate
#print axioms su2_mandelstam_trace
#print axioms su2_complex_wilson_root_fusion

end YMUIC.I7
