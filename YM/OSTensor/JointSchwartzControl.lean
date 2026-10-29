import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false
namespace YMUIC.OSTensor

/-- A nonhomogeneous joint Schwartz control retaining all derivative orders
through `m`, both near the origin and with the requested spatial weight. -/
noncomputable def jointSchwartzControl (r q m : ℕ) :
    Seminorm ℂ (SchwartzMap (EuclideanSpace ℝ (Fin (4 * r))) ℂ) :=
  ∑ i ∈ Finset.range (m + 1), (SchwartzMap.seminorm ℂ 0 i + SchwartzMap.seminorm ℂ q i)

/-- The joint control is continuous and dominates every included unweighted
and weighted derivative seminorm. -/
theorem joint_schwartz_control (r q m : ℕ) :
    Continuous (jointSchwartzControl r q m) ∧
    ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (4 * r))) ℂ) (i : ℕ), i ≤ m →
      SchwartzMap.seminorm ℂ 0 i f ≤ jointSchwartzControl r q m f ∧
      SchwartzMap.seminorm ℂ q i f ≤ jointSchwartzControl r q m f := by
  have he (f : SchwartzMap (EuclideanSpace ℝ (Fin (4 * r))) ℂ) :
      jointSchwartzControl r q m f = ∑ i ∈ Finset.range (m + 1),
        (SchwartzMap.seminorm ℂ 0 i f + SchwartzMap.seminorm ℂ q i f) := by
    simp [jointSchwartzControl]
  constructor
  · simp_rw [show (jointSchwartzControl r q m : _ → ℝ) = _ from funext he]
    apply continuous_finsetSum
    intro i _
    exact ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin (4 * r))) ℂ).continuous_seminorm
      (0, i)).add
      ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin (4 * r))) ℂ).continuous_seminorm (q, i))
  · intro f i hi
    rw [he]
    have hb := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (m + 1)) =>
        add_nonneg (apply_nonneg (SchwartzMap.seminorm ℂ 0 j) f)
          (apply_nonneg (SchwartzMap.seminorm ℂ q j) f))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact ⟨(le_add_of_nonneg_right (apply_nonneg (SchwartzMap.seminorm ℂ q i) f)).trans hb,
      (le_add_of_nonneg_left (apply_nonneg (SchwartzMap.seminorm ℂ 0 i) f)).trans hb⟩

end YMUIC.OSTensor
