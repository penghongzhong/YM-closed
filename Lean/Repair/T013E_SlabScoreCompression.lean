import Mathlib

set_option autoImplicit false

/-! Hilbert-space compression identity. No slab vector is identified with a slice vector. -/
namespace YMUICV128.Repair.T013E

theorem slab_score_compression {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (raw projected g0 gt : E)
    (hzero : inner ℝ (raw - projected) g0 = 0)
    (hterminal : inner ℝ raw gt = 0) :
    inner ℝ projected (g0 - gt) = inner ℝ raw g0 + inner ℝ (raw - projected) gt := by
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

theorem centered_residual_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (residual gt gt0 : E) (horth : inner ℝ residual gt0 = 0) :
    inner ℝ residual gt = inner ℝ residual (gt - gt0) := by
  rw [inner_sub_right, horth, sub_zero]

theorem corrected_deficit_arithmetic (lambda r : ℝ) :
    lambda * (1 - r) = lambda + (-lambda * r) := by ring

theorem nonzero_missing_correction (lambda r : ℝ) (hl : 0 < lambda) (hr : 0 < r) :
    lambda * (1 - r) < lambda := by nlinarith [mul_pos hl hr]

#print axioms slab_score_compression
#print axioms centered_residual_pairing
#print axioms corrected_deficit_arithmetic
#print axioms nonzero_missing_correction
end YMUICV128.Repair.T013E
