import Mathlib

set_option autoImplicit false

namespace YMUICV128.Repair.T013C

noncomputable def qmul (a b : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3,
    a 0 * b 1 + a 1 * b 0 + a 2 * b 3 - a 3 * b 2,
    a 0 * b 2 - a 1 * b 3 + a 2 * b 0 + a 3 * b 1,
    a 0 * b 3 + a 1 * b 2 - a 2 * b 1 + a 3 * b 0]

noncomputable def commutator (c s : ℝ) : Fin 4 → ℝ :=
  qmul (qmul (qmul ![c, 0, s, 0] ![c, s, 0, 0]) ![c, 0, -s, 0]) ![c, -s, 0, 0]

noncomputable def qnormSq (q : Fin 4 → ℝ) : ℝ :=
  q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2

theorem commutator_scalar (c s : ℝ) :
    commutator c s 0 = (c ^ 2 + s ^ 2) ^ 2 - 2 * s ^ 4 := by
  simp [commutator, qmul]
  ring

theorem commutator_normSq (c s : ℝ) :
    qnormSq (commutator c s) = (c ^ 2 + s ^ 2) ^ 4 := by
  simp [qnormSq, commutator, qmul]
  ring

theorem unit_commutator_defect (c s : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) :
    2 * (1 - commutator c s 0) = 4 * s ^ 4 := by
  rw [commutator_scalar, hunit]
  ring

theorem pauli_axis_average (s : ℝ) :
    (∑ a : Fin 3, ∑ b : Fin 3, if a = b then (0 : ℝ) else 4 * s ^ 4) / 9 =
      (8 / 3 : ℝ) * s ^ 4 := by
  norm_num [Fin.sum_univ_succ]
  ring

#print axioms commutator_scalar
#print axioms commutator_normSq
#print axioms unit_commutator_defect
#print axioms pauli_axis_average
end YMUICV128.Repair.T013C
