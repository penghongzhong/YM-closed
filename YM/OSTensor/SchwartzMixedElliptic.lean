import YM.OSTensor.SchwartzEllipticStep

set_option autoImplicit false
namespace YMUIC.OSTensor

/-- Compose the actual fourth-order coordinate operators in the given order. -/
noncomputable def schwartzMixedElliptic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : List E) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  match v with
  | [] => f
  | a :: w => schwartzEllipticStep a (schwartzMixedElliptic w f)

/-- The mixed operator has exponential, rather than factorial, cost in the number of directions. -/
theorem schwartz_mixed_elliptic_seminorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (v : List E) (hv : ∀ a ∈ v, ‖a‖ ≤ 1) (q m : ℕ) :
    SchwartzMap.seminorm ℂ q m (schwartzMixedElliptic v f) ≤
      (4 : ℝ) ^ v.length * ∑ j ∈ Finset.range (m + 4 * v.length + 1),
        SchwartzMap.seminorm ℂ q j f := by
  have hmono {a b : ℕ} (h : a ≤ b) :
      (∑ j ∈ Finset.range (a + 1), SchwartzMap.seminorm ℂ q j f) ≤
        ∑ j ∈ Finset.range (b + 1), SchwartzMap.seminorm ℂ q j f :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => apply_nonneg _ _)
  induction v generalizing m with
  | nil =>
    simp only [schwartzMixedElliptic, List.length_nil, mul_zero, add_zero, pow_zero, one_mul]
    exact Finset.single_le_sum (fun j _ => apply_nonneg (SchwartzMap.seminorm ℂ q j) f)
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
  | cons a w ih =>
    have hw : ∀ b ∈ w, ‖b‖ ≤ 1 := fun b hb => hv b (List.mem_cons_of_mem a hb)
    have hb := schwartz_elliptic_step_seminorm (schwartzMixedElliptic w f) a
      (hv a (List.mem_cons_self)) q m
    have h0 := (ih hw m).trans (mul_le_mul_of_nonneg_left
      (hmono (show m + 4 * w.length ≤ m + 4 * (w.length + 1) by omega)) (by positivity))
    have h2 := (ih hw (m + 2)).trans (mul_le_mul_of_nonneg_left
      (hmono (show m + 2 + 4 * w.length ≤ m + 4 * (w.length + 1) by omega)) (by positivity))
    have h4 := (ih hw (m + 4)).trans (mul_le_mul_of_nonneg_left
      (hmono (show m + 4 + 4 * w.length ≤ m + 4 * (w.length + 1) by omega)) (by positivity))
    simp only [schwartzMixedElliptic, List.length_cons, pow_succ]
    nlinarith
end YMUIC.OSTensor
