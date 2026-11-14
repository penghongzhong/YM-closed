import YM.OSTensor.SchwartzDirectionalSeminorm

set_option autoImplicit false
namespace YMUIC.OSTensor
open LineDeriv

/-- Repeated directional derivatives retain the sharp seminorm shift. -/
theorem schwartz_iterated_directional_seminorm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (v : E) (hv : ‖v‖ ≤ 1) (q m j : ℕ) :
    SchwartzMap.seminorm ℂ q m ((lineDerivOp v)^[j] f) ≤
      SchwartzMap.seminorm ℂ q (m + j) f := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (schwartz_directional_seminorm _ v hv q m).trans
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using ih (m + 1))
end YMUIC.OSTensor
