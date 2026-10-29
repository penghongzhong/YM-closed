import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

namespace YMUIC.Reflection

/-- The actual reflection pairing of complex-valued observables. -/
def reflectionPair {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (θ : X → X) (F G : X → ℂ) : ℂ :=
  ∫ x, conj (F (θ x)) * G x ∂μ

/-- Nonnegativity as a real complex number: the imaginary part is not discarded. -/
def ComplexNonnegative (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

/-- Each element of the finite-cutoff positive-time algebra is genuinely
measurable and bounded. Bounds may depend on the cutoff and on the observable. -/
def BoundedMeasurableAlgebra {X : Type*} [MeasurableSpace X]
    (S : Subalgebra ℂ (X → ℂ)) : Prop :=
  ∀ F ∈ S, Measurable F ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖F x‖ ≤ M

/-- Integrability is derived from finite-cutoff boundedness, so the default
Bochner value for a nonintegrable function is never used as positivity. -/
theorem reflection_product_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (θ : X → X) (hθ : Measurable θ)
    (S : Subalgebra ℂ (X → ℂ)) (hreg : BoundedMeasurableAlgebra S)
    {F G : X → ℂ} (hF : F ∈ S) (hG : G ∈ S) :
    Integrable (fun x => conj (F (θ x)) * G x) μ := by
  obtain ⟨hFm, M, hM, hFb⟩ := hreg F hF
  obtain ⟨hGm, N, hN, hGb⟩ := hreg G hG
  have hmeas : Measurable (fun x => conj (F (θ x)) * G x) :=
    (Complex.continuous_conj.measurable.comp (hFm.comp hθ)).mul hGm
  apply (integrable_const (M*N)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  calc
    ‖conj (F (θ x)) * G x‖ = ‖F (θ x)‖ * ‖G x‖ := by simp
    _ ≤ M * N := mul_le_mul (hFb _) (hGb _) (norm_nonneg _) hM

/-- Arbitrary cutoff-dependent source mixing. No bound, invertibility, or
unitarity of the mixing matrix is required for reflection positivity. -/
def mixedField {X σ τ : Type*} [Fintype τ]
    (O : τ → X → ℂ) (B : τ → σ → ℂ) (a : σ) : X → ℂ :=
  ∑ e, B e a • O e

theorem mixedField_mem {X σ τ : Type*} [Fintype τ]
    (S : Subalgebra ℂ (X → ℂ)) (O : τ → X → ℂ) (B : τ → σ → ℂ)
    (hO : ∀ e, O e ∈ S) (a : σ) : mixedField O B a ∈ S := by
  exact S.sum_mem (fun e _ => S.smul_mem (hO e) (B e a))

/-- A finite monomial in the same renormalized fields. -/
def monomialField {X σ : Type*} (R : σ → X → ℂ) (d : σ →₀ ℕ) : X → ℂ :=
  ∏ a ∈ d.support, R a ^ d a

/-- Actual evaluation of a finite polynomial, not an abstract positivity label. -/
def polynomialField {X σ : Type*} (R : σ → X → ℂ) (p : MvPolynomial σ ℂ) : X → ℂ :=
  fun x => MvPolynomial.eval (fun a => R a x) p

theorem monomialField_mem {X σ : Type*} (S : Subalgebra ℂ (X → ℂ))
    (R : σ → X → ℂ) (hR : ∀ a, R a ∈ S) (d : σ →₀ ℕ) :
    monomialField R d ∈ S := by
  exact S.prod_mem (fun a _ => S.pow_mem (hR a) _)

theorem polynomialField_expansion {X σ : Type*}
    (R : σ → X → ℂ) (p : MvPolynomial σ ℂ) :
    polynomialField R p = ∑ d ∈ p.support, p.coeff d • monomialField R d := by
  classical
  funext x
  simp [polynomialField, monomialField, MvPolynomial.eval_eq,
    Finset.sum_apply, Finset.prod_apply]

theorem polynomialField_mem {X σ : Type*} (S : Subalgebra ℂ (X → ℂ))
    (R : σ → X → ℂ) (hR : ∀ a, R a ∈ S) (p : MvPolynomial σ ℂ) :
    polynomialField R p ∈ S := by
  rw [polynomialField_expansion]
  exact S.sum_mem (fun d _ => S.smul_mem (monomialField_mem S R hR d) _)

/-- The exact quadratic/Gram expansion including conjugate coefficients. -/
theorem reflectionPair_polynomial_expansion {X σ : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (θ : X → X) (hθ : Measurable θ)
    (S : Subalgebra ℂ (X → ℂ)) (hreg : BoundedMeasurableAlgebra S)
    (R : σ → X → ℂ) (hR : ∀ a, R a ∈ S) (p q : MvPolynomial σ ℂ) :
    reflectionPair μ θ (polynomialField R p) (polynomialField R q) =
      ∑ d ∈ p.support, ∑ e ∈ q.support,
        (conj (p.coeff d) * q.coeff e) *
          reflectionPair μ θ (monomialField R d) (monomialField R e) := by
  classical
  have hint (d e : σ →₀ ℕ) :
      Integrable (fun x => (conj (p.coeff d) * q.coeff e) *
        (conj (monomialField R d (θ x)) * monomialField R e x)) μ :=
    (reflection_product_integrable μ θ hθ S hreg
      (monomialField_mem S R hR d) (monomialField_mem S R hR e)).const_mul _
  have hexpand (x : X) :
      conj (polynomialField R p (θ x)) * polynomialField R q x =
      ∑ d ∈ p.support, ∑ e ∈ q.support,
        (conj (p.coeff d) * q.coeff e) *
          (conj (monomialField R d (θ x)) * monomialField R e x) := by
    simp only [polynomialField_expansion, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    ring
  unfold reflectionPair
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun d _ => integrable_finset_sum _ (fun e _ => hint d e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_finset_sum _ (fun e _ => hint d e)]
  apply Finset.sum_congr rfl
  intro e he
  exact integral_const_mul _ _

/-- The cutoff positivity premise is used only on the original algebra.
Mixed fields and every polynomial in them are proved to stay in that algebra. -/
theorem cutoff_polynomial_reflection_positive {X σ τ : Type*}
    [MeasurableSpace X] [Fintype τ]
    (μ : Measure X) (θ : X → X) (S : Subalgebra ℂ (X → ℂ))
    (hRP : ∀ F ∈ S, ComplexNonnegative (reflectionPair μ θ F F))
    (O : τ → X → ℂ) (B : τ → σ → ℂ) (hO : ∀ e, O e ∈ S)
    (p : MvPolynomial σ ℂ) :
    ComplexNonnegative
      (reflectionPair μ θ (polynomialField (mixedField O B) p)
        (polynomialField (mixedField O B) p)) := by
  exact hRP _ (polynomialField_mem S _ (mixedField_mem S O B hO) p)

end YMUIC.Reflection
