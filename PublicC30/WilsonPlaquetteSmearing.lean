import YM.Wilson.RootBound
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false

namespace YMUIC.OSTensor
open YMUICV128.Section03

/-- Finite-volume Wilson root source smeared against a *genuine* complex
Schwartz test function on Euclidean R⁴. The regulator spacing carries
the correct four-dimensional cell-volume factor. -/
noncomputable def wilsonPlaquetteSchwartzSmear
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4)) (a : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) : ℂ :=
  ∑ p ∈ S,
    ((a ^ 4 * wilsonRoot (U p) : ℝ) : ℂ) * f (position p)

/-- Pointwise Wilson root amplitude bound, with *no* arbitrary source norm
assumption. Uses the exact SU(2) plaquette root 2-Re(tr U) ∈ [0,4]. -/
theorem wilsonPlaquetteSchwartz_term_bound
    {P : Type*} (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4))
    (a : ℝ) (ha : 0 ≤ a) (p : P)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    ‖((a ^ 4 * wilsonRoot (U p) : ℝ) : ℂ) * f (position p)‖ ≤
      (4 * a ^ 4) * (SchwartzMap.seminorm ℝ 0 0) f := by
  obtain ⟨hw0, hw4⟩ := wilsonRoot_bounds (U p)
  have ha4 : 0 ≤ a ^ 4 := pow_nonneg ha _
  have hcoeff : a ^ 4 * wilsonRoot (U p) ≤ 4 * a ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hw4 ha4]
  have hf := SchwartzMap.norm_le_seminorm ℝ f (position p)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ha4 hw0)]
  calc
    (a ^ 4 * wilsonRoot (U p)) * ‖f (position p)‖
        ≤ (4 * a ^ 4) * ‖f (position p)‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ ≤ (4 * a ^ 4) * (SchwartzMap.seminorm ℝ 0 0) f :=
      mul_le_mul_of_nonneg_left hf (by positivity)

/-- The finite Wilson plaquette source is controlled by an *explicit*
Schwartz seminorm; no abstract local source operator bound is imported. -/
theorem wilsonPlaquetteSchwartz_finite_bound
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4))
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    ‖wilsonPlaquetteSchwartzSmear S U position a f‖ ≤
      (4 * a ^ 4) * (S.card : ℝ) *
        (SchwartzMap.seminorm ℝ 0 0) f := by
  classical
  unfold wilsonPlaquetteSchwartzSmear
  calc
    ‖∑ p ∈ S, ((a ^ 4 * wilsonRoot (U p) : ℝ) : ℂ) * f (position p)‖
        ≤ ∑ p ∈ S,
            ‖((a ^ 4 * wilsonRoot (U p) : ℝ) : ℂ) * f (position p)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, (4 * a ^ 4) * (SchwartzMap.seminorm ℝ 0 0) f := by
      exact Finset.sum_le_sum (fun p hp =>
        wilsonPlaquetteSchwartz_term_bound U position a ha p f)
    _ = (4 * a ^ 4) * (S.card : ℝ) *
        (SchwartzMap.seminorm ℝ 0 0) f := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Uniformity in volume, regulator and gauge holonomies follows from
the *explicit physical plaquette packing bound* a⁴ |S| ≤ V. This packing
hypothesis remains an independent geometry obligation, not a Wilson
field estimate and not an axiom. -/
theorem wilsonPlaquetteSchwartz_uniform_bound
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4))
    (a V : ℝ) (ha : 0 ≤ a)
    (hpacking : a ^ 4 * (S.card : ℝ) ≤ V)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    ‖wilsonPlaquetteSchwartzSmear S U position a f‖ ≤
      (4 * V) * (SchwartzMap.seminorm ℝ 0 0) f := by
  have hq : 0 ≤ (SchwartzMap.seminorm ℝ 0 0) f := apply_nonneg _ _
  calc
    _ ≤ (4 * a ^ 4) * (S.card : ℝ) *
        (SchwartzMap.seminorm ℝ 0 0) f :=
      wilsonPlaquetteSchwartz_finite_bound S U position a ha f
    _ = (4 * (a ^ 4 * (S.card : ℝ))) *
        (SchwartzMap.seminorm ℝ 0 0) f := by ring
    _ ≤ (4 * V) * (SchwartzMap.seminorm ℝ 0 0) f :=
      mul_le_mul_of_nonneg_right (by nlinarith [hpacking]) hq

end YMUIC.OSTensor
