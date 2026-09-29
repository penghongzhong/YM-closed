import Mathlib

set_option autoImplicit false

namespace YMUICV128.Repair.T013B

theorem four_vector_square {E : Type*} [SeminormedAddCommGroup E]
    (a b c d : E) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have ht : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    have h1 := norm_add_le a b
    have h2 := norm_add_le (a + b) c
    have h3 := norm_add_le (a + b + c) d
    linarith
  have hs := mul_self_le_mul_self (norm_nonneg (a + b + c + d)) ht
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
    sq_nonneg (‖a‖ - ‖d‖), sq_nonneg (‖b‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

theorem cycle_identity {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T1 T2 T3 T4 : E →ₗ[ℝ] E) (v0 v1 v2 v3 : E) :
    v0 - T1 (T2 (T3 (T4 v0))) =
      (v0 - T1 v1) + T1 (v1 - T2 v2) + T1 (T2 (v2 - T3 v3)) +
        T1 (T2 (T3 (v3 - T4 v0))) := by
  simp only [map_sub]
  abel

theorem unitary_cycle_square {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T1 T2 T3 T4 : E ≃ₗᵢ[ℝ] E) (v0 v1 v2 v3 : E) :
    ‖v0 - T1 (T2 (T3 (T4 v0)))‖ ^ 2 ≤
      4 * (‖v0 - T1 v1‖ ^ 2 + ‖v1 - T2 v2‖ ^ 2 +
        ‖v2 - T3 v3‖ ^ 2 + ‖v3 - T4 v0‖ ^ 2) := by
  have he := cycle_identity T1.toLinearEquiv.toLinearMap T2.toLinearEquiv.toLinearMap
    T3.toLinearEquiv.toLinearMap T4.toLinearEquiv.toLinearMap v0 v1 v2 v3
  change v0 - T1 (T2 (T3 (T4 v0))) = _ at he
  rw [he]
  have h := four_vector_square (v0 - T1 v1) (T1 (v1 - T2 v2))
    (T1 (T2 (v2 - T3 v3))) (T1 (T2 (T3 (v3 - T4 v0))))
  simpa only [LinearIsometryEquiv.norm_map] using h

#print axioms four_vector_square
#print axioms cycle_identity
#print axioms unitary_cycle_square
end YMUICV128.Repair.T013B
