import Mathlib

set_option autoImplicit false

/-!
# U2 source analyticity: Banach-space differentiable tsum engine

This is a thin exact wrapper around mathlib's
hasFDerivAt_tsum_of_isPreconnected, specialized to the joint source space
C x C. It is fully multivariable: no separate-holomorphy shortcut is used.
-/

namespace YMUICV128.Section03.T008C

theorem joint_hasFDerivAt_tsum
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (F' : ι → (ℂ × ℂ) → (ℂ × ℂ →L[ℂ] ℂ))
    (u : ι → ℝ)
    (U : Set (ℂ × ℂ))
    (hu : Summable u)
    (hUopen : IsOpen U)
    (hUpre : IsPreconnected U)
    (hF :
      ∀ i x, x ∈ U → HasFDerivAt (F i) (F' i x) x)
    (hF' :
      ∀ i x, x ∈ U → ‖F' i x‖ ≤ u i)
    (x0 : ℂ × ℂ)
    (hx0 : x0 ∈ U)
    (hsum0 : Summable (fun i => F i x0))
    (x : ℂ × ℂ)
    (hx : x ∈ U) :
    HasFDerivAt
      (fun y => ∑' i, F i y)
      (∑' i, F' i x) x := by
  exact hasFDerivAt_tsum_of_isPreconnected
    hu hUopen hUpre hF hF' hx0 hsum0 hx

theorem joint_differentiableOn_tsum
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (F' : ι → (ℂ × ℂ) → (ℂ × ℂ →L[ℂ] ℂ))
    (u : ι → ℝ)
    (U : Set (ℂ × ℂ))
    (hu : Summable u)
    (hUopen : IsOpen U)
    (hUpre : IsPreconnected U)
    (hF :
      ∀ i x, x ∈ U → HasFDerivAt (F i) (F' i x) x)
    (hF' :
      ∀ i x, x ∈ U → ‖F' i x‖ ≤ u i)
    (x0 : ℂ × ℂ)
    (hx0 : x0 ∈ U)
    (hsum0 : Summable (fun i => F i x0)) :
    DifferentiableOn ℂ (fun y => ∑' i, F i y) U := by
  intro x hx
  exact (joint_hasFDerivAt_tsum
    F F' u U hu hUopen hUpre hF hF'
    x0 hx0 hsum0 x hx).differentiableAt.differentiableWithinAt

theorem joint_holomorphicOn_tsum
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (F' : ι → (ℂ × ℂ) → (ℂ × ℂ →L[ℂ] ℂ))
    (u : ι → ℝ)
    (U : Set (ℂ × ℂ))
    (hu : Summable u)
    (hUopen : IsOpen U)
    (hUpre : IsPreconnected U)
    (hF :
      ∀ i x, x ∈ U → HasFDerivAt (F i) (F' i x) x)
    (hF' :
      ∀ i x, x ∈ U → ‖F' i x‖ ≤ u i)
    (x0 : ℂ × ℂ)
    (hx0 : x0 ∈ U)
    (hsum0 : Summable (fun i => F i x0)) :
    DifferentiableOn ℂ (fun y => ∑' i, F i y) U :=
  joint_differentiableOn_tsum
    F F' u U hu hUopen hUpre hF hF'
    x0 hx0 hsum0

#print axioms joint_hasFDerivAt_tsum
#print axioms joint_differentiableOn_tsum
#print axioms joint_holomorphicOn_tsum

end YMUICV128.Section03.T008C
