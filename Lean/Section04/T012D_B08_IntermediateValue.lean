import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section04.T012D

theorem endpoint_shooting (Phi : ℝ → ℝ) (a b xs : ℝ)
    (hab : a ≤ b) (hcont : ContinuousOn Phi (Set.Icc a b))
    (hminus : Phi a < xs) (hplus : xs < Phi b) :
    ∃ u ∈ Set.Ioo a b, Phi u = xs := by
  obtain ⟨u, hu, hhit⟩ := intermediate_value_Icc hab hcont ⟨hminus.le, hplus.le⟩
  have hua : a < u := by
    by_contra hf
    have heq : u = a := le_antisymm (le_of_not_gt hf) hu.1
    subst u
    linarith
  have hub : u < b := by
    by_contra hf
    have heq : u = b := le_antisymm hu.2 (le_of_not_gt hf)
    subst u
    linarith
  exact ⟨u, ⟨hua, hub⟩, hhit⟩

#print axioms endpoint_shooting

end YMUICV128.Section04.T012D
