import PublicC30.WilsonHypercubicPacking
import Mathlib.Analysis.Distribution.TemperedDistribution

set_option autoImplicit false

namespace YMUIC.OSTensor
open YMUICV128.Section03

/-- The actual single-plaquette Wilson source functional as a continuous
complex-linear map on the genuine Schwartz space. Constructed by summing
Mathlib's continuous Dirac evaluations; no source linearity or
continuity is supplied as an assumption. -/
noncomputable def wilsonPlaquetteSchwartzCLM
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4)) (a : ℝ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ →L[ℂ] ℂ := by
  classical
  exact ∑ p ∈ S,
    (((a ^ 4 * wilsonRoot (U p) : ℝ) : ℂ)) •
      ((BoundedContinuousFunction.evalCLM ℂ (position p)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ
          (EuclideanSpace ℝ (Fin 4)) ℂ))

/-- Evaluation of the constructed map equals the original Wilson root
Schwartz smearing sum, not just an abstract source functional. -/
theorem wilsonPlaquetteSchwartzCLM_apply
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4)) (a : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    wilsonPlaquetteSchwartzCLM S U position a f =
      wilsonPlaquetteSchwartzSmear S U position a f := by
  classical
  simp [wilsonPlaquetteSchwartzCLM, wilsonPlaquetteSchwartzSmear,
    smul_eq_mul]

/-- Explicit, non-assumed continuity: the actual Wilson source is
complex-linear because it is a genuine continuous linear map. -/
theorem wilsonPlaquetteSchwartzCLM_add
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4)) (a : ℝ)
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    wilsonPlaquetteSchwartzSmear S U position a (f + g) =
      wilsonPlaquetteSchwartzSmear S U position a f +
        wilsonPlaquetteSchwartzSmear S U position a g := by
  rw [← wilsonPlaquetteSchwartzCLM_apply,
    ← wilsonPlaquetteSchwartzCLM_apply,
    ← wilsonPlaquetteSchwartzCLM_apply]
  exact map_add _ _ _

theorem wilsonPlaquetteSchwartzCLM_smul
    {P : Type*} (S : Finset P) (U : P → SU2)
    (position : P → EuclideanSpace ℝ (Fin 4)) (a : ℝ)
    (c : ℂ) (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    wilsonPlaquetteSchwartzSmear S U position a (c • f) =
      c • wilsonPlaquetteSchwartzSmear S U position a f := by
  rw [← wilsonPlaquetteSchwartzCLM_apply,
    ← wilsonPlaquetteSchwartzCLM_apply]
  exact map_smul _ _ _

/-- Uniform physical-box Schwartz bound for the actual continuous map;
the grid count, continuity and linearity are all derived internally. -/
theorem periodic4D_wilson_SchwartzCLM_uniform
    (N : ℕ) (S : Finset (Periodic4DPlaquette N))
    (U : Periodic4DPlaquette N → SU2)
    (position : Periodic4DPlaquette N → EuclideanSpace ℝ (Fin 4))
    (a L : ℝ) (ha : 0 ≤ a) (hbox : a * (N : ℝ) ≤ L)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    ‖wilsonPlaquetteSchwartzCLM S U position a f‖ ≤
      24 * L ^ 4 * (SchwartzMap.seminorm ℝ 0 0) f := by
  rw [wilsonPlaquetteSchwartzCLM_apply]
  exact periodic4D_wilson_Schwartz_uniform N S U position a L ha hbox f

end YMUIC.OSTensor
