import Mathlib

set_option autoImplicit false

/-!
# U2 source analyticity: final joint-holomorphic assembly

This file performs only the final assembly of the already certified ingredients:
* pointwise complex Frechet derivatives on C x C;
* a summable derivative majorant;
* open/preconnected polydiscs;
* a summable tree majorant for normal convergence.

The variable r here is the paper's smaller radius r' (0 < r' < r).
-/

namespace YMUICV128.Section03.T008F

def polydisc (r : ℝ) : Set (ℂ × ℂ) :=
  Metric.ball (0 : ℂ) r ×ˢ Metric.ball (0 : ℂ) r

def closedPolydisc (r : ℝ) : Set (ℂ × ℂ) :=
  Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) r

theorem source_series_joint_holomorphic
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (F' : ι → (ℂ × ℂ) → ((ℂ × ℂ) →L[ℂ] ℂ))
    (derivMajor : ι → ℝ)
    (r : ℝ)
    (hr : 0 < r)
    (hDerivMajor : Summable derivMajor)
    (hF :
      ∀ i z, z ∈ polydisc r →
        HasFDerivAt (F i) (F' i z) z)
    (hF' :
      ∀ i z, z ∈ polydisc r →
        ‖F' i z‖ ≤ derivMajor i)
    (hzero : ∀ i, F i (0, 0) = 0) :
    DifferentiableOn ℂ
      (fun z => ∑' i, F i z)
      (polydisc r) := by
  have hopen : IsOpen (polydisc r) := by
    exact Metric.isOpen_ball.prod Metric.isOpen_ball
  have hpre : IsPreconnected (polydisc r) := by
    exact ((convex_ball (0 : ℂ) r).prod
      (convex_ball (0 : ℂ) r)).isPreconnected
  have h0 : ((0, 0) : ℂ × ℂ) ∈ polydisc r := by
    constructor <;>
      simpa [polydisc] using
        (Metric.mem_ball_self hr : (0 : ℂ) ∈ Metric.ball 0 r)
  have hsum0 :
      Summable (fun i => F i ((0, 0) : ℂ × ℂ)) := by
    simpa [hzero] using
      (summable_zero : Summable (fun _ : ι => (0 : ℂ)))
  intro z hz
  exact
    (hasFDerivAt_tsum_of_isPreconnected
      hDerivMajor hopen hpre hF hF' h0 hsum0 hz).differentiableAt.differentiableWithinAt

theorem source_series_uniform_on_closed_polydisc
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (treeWeight : ι → ℝ)
    (K r : ℝ)
    (htree : Summable treeWeight)
    (hbound :
      ∀ i z, z ∈ closedPolydisc r →
        ‖F i z‖ ≤ K * treeWeight i) :
    TendstoUniformlyOn
      (fun T : Finset ι => fun z => ∑ i ∈ T, F i z)
      (fun z => ∑' i, F i z)
      Filter.atTop
      (closedPolydisc r) := by
  exact tendstoUniformlyOn_tsum
    (htree.mul_left K) hbound

theorem source_series_norm_tsum_le
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (treeWeight : ι → ℝ)
    (K A r : ℝ)
    (htree : Summable treeWeight)
    (hK0 : 0 ≤ K)
    (htreeTotal : (∑' i, treeWeight i) ≤ A)
    (hbound :
      ∀ i z, z ∈ closedPolydisc r →
        ‖F i z‖ ≤ K * treeWeight i)
    {z : ℂ × ℂ}
    (hz : z ∈ closedPolydisc r) :
    (∑' i, ‖F i z‖) ≤ K * A := by
  have hmajor : Summable (fun i => K * treeWeight i) :=
    htree.mul_left K
  have hnorm : Summable (fun i => ‖F i z‖) :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun i => hbound i z hz)
      hmajor
  calc
    (∑' i, ‖F i z‖)
        ≤ ∑' i, K * treeWeight i :=
      hnorm.tsum_le_tsum
        (fun i => hbound i z hz) hmajor
    _ = K * (∑' i, treeWeight i) := by
      rw [tsum_mul_left]
    _ ≤ K * A :=
      mul_le_mul_of_nonneg_left htreeTotal hK0

theorem source_analyticity_full_assembly
    {ι : Type*}
    (F : ι → (ℂ × ℂ) → ℂ)
    (F' : ι → (ℂ × ℂ) → ((ℂ × ℂ) →L[ℂ] ℂ))
    (derivMajor treeWeight : ι → ℝ)
    (K A r : ℝ)
    (hr : 0 < r)
    (hDerivMajor : Summable derivMajor)
    (hF :
      ∀ i z, z ∈ polydisc r →
        HasFDerivAt (F i) (F' i z) z)
    (hF' :
      ∀ i z, z ∈ polydisc r →
        ‖F' i z‖ ≤ derivMajor i)
    (hzero : ∀ i, F i (0, 0) = 0)
    (htree : Summable treeWeight)
    (hK0 : 0 ≤ K)
    (htreeTotal : (∑' i, treeWeight i) ≤ A)
    (hbound :
      ∀ i z, z ∈ closedPolydisc r →
        ‖F i z‖ ≤ K * treeWeight i) :
    DifferentiableOn ℂ
        (fun z => ∑' i, F i z)
        (polydisc r)
      ∧
    TendstoUniformlyOn
        (fun T : Finset ι => fun z => ∑ i ∈ T, F i z)
        (fun z => ∑' i, F i z)
        Filter.atTop
        (closedPolydisc r)
      ∧
    ∀ z ∈ closedPolydisc r,
      (∑' i, ‖F i z‖) ≤ K * A := by
  refine ⟨
    source_series_joint_holomorphic
      F F' derivMajor r hr hDerivMajor hF hF' hzero,
    source_series_uniform_on_closed_polydisc
      F treeWeight K r htree hbound,
    ?_⟩
  intro z hz
  exact source_series_norm_tsum_le
    F treeWeight K A r htree hK0 htreeTotal hbound hz

#print axioms source_series_joint_holomorphic
#print axioms source_series_uniform_on_closed_polydisc
#print axioms source_series_norm_tsum_le
#print axioms source_analyticity_full_assembly

end YMUICV128.Section03.T008F
