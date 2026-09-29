import Mathlib

set_option autoImplicit false

/-!
# U2 source analyticity: polydisc normal-convergence assembly

Generic multivariable engine on C x C.
-/

namespace YMUICV128.Section03.T008D

def polydisc (r : ℝ) : Set (ℂ × ℂ) :=
  Metric.ball (0 : ℂ) r ×ˢ Metric.ball (0 : ℂ) r

theorem isOpen_polydisc (r : ℝ) :
    IsOpen (polydisc r) := by
  exact Metric.isOpen_ball.prod Metric.isOpen_ball

theorem isPreconnected_polydisc (r : ℝ) :
    IsPreconnected (polydisc r) := by
  exact ((convex_ball (0 : ℂ) r).prod
    (convex_ball (0 : ℂ) r)).isPreconnected

theorem zero_mem_polydisc {r : ℝ} (hr : 0 < r) :
    ((0,0) : ℂ × ℂ) ∈ polydisc r := by
  constructor <;> simpa [polydisc] using (Metric.mem_ball_self hr : (0 : ℂ) ∈ Metric.ball 0 r)

theorem holomorphicOn_tsum_on_polydisc
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (F' : ι → (ℂ × ℂ) → (ℂ × ℂ →L[ℂ] ℂ))
    (major : ι → ℝ)
    (r : ℝ)
    (hr : 0 < r)
    (hmajor : Summable major)
    (hF :
      ∀ i z, z ∈ polydisc r →
        HasFDerivAt (F i) (F' i z) z)
    (hF' :
      ∀ i z, z ∈ polydisc r →
        ‖F' i z‖ ≤ major i)
    (hzero : ∀ i, F i (0,0) = 0) :
    DifferentiableOn ℂ
      (fun z => ∑' i, F i z)
      (polydisc r) := by
  have hsum0 : Summable (fun i => F i ((0,0) : ℂ × ℂ)) := by
    simpa [hzero] using
      (summable_zero : Summable (fun _ : ι => (0 : ℂ)))
  have hdiff :
      DifferentiableOn ℂ
        (fun z => ∑' i, F i z)
        (polydisc r) := by
    intro z hz
    exact
      (hasFDerivAt_tsum_of_isPreconnected
        hmajor
        (isOpen_polydisc r)
        (isPreconnected_polydisc r)
        hF hF'
        (zero_mem_polydisc hr)
        hsum0
        hz).differentiableAt.differentiableWithinAt
  exact hdiff

theorem tendstoUniformlyOn_tsum_of_tree_majorant
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (treeWeight : ι → ℝ)
    (K : ℝ)
    (S : Set (ℂ × ℂ))
    (htree : Summable treeWeight)
    (hbound :
      ∀ i z, z ∈ S →
        ‖F i z‖ ≤ K * treeWeight i) :
    TendstoUniformlyOn
      (fun T : Finset ι => fun z => ∑ i ∈ T, F i z)
      (fun z => ∑' i, F i z)
      Filter.atTop S := by
  exact tendstoUniformlyOn_tsum
    (htree.mul_left K) hbound

#print axioms isOpen_polydisc
#print axioms isPreconnected_polydisc
#print axioms holomorphicOn_tsum_on_polydisc
#print axioms tendstoUniformlyOn_tsum_of_tree_majorant

end YMUICV128.Section03.T008D
