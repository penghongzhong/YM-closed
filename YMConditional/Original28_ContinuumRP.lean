import YMConditional.Original28_ReflectionAlgebra

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

namespace YMUIC.Reflection

/-- The continuum reflected polynomial pairing assembled from the SAME
joint limiting monomial moments. This is an explicit finite double sum. -/
def continuumReflectionPair {σ : Type*}
    (C : (σ →₀ ℕ) → (σ →₀ ℕ) → ℂ)
    (p q : MvPolynomial σ ℂ) : ℂ :=
  ∑ d ∈ p.support, ∑ e ∈ q.support,
    (conj (p.coeff d) * q.coeff e) * C d e

/-- Complex positivity is closed under arbitrary nontrivial filter limits.
Both real and imaginary parts are tracked. -/
theorem complexNonnegative_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {z : ι → ℂ} {w : ℂ} (hz : Tendsto z l (𝓝 w))
    (hpos : ∀ᶠ i in l, ComplexNonnegative (z i)) :
    ComplexNonnegative w := by
  have him : w.im = 0 :=
    (isClosed_eq Complex.continuous_im continuous_const).mem_of_tendsto hz
      (hpos.mono (fun _ h => h.1))
  have hre : 0 ≤ w.re :=
    ge_of_tendsto (Complex.continuous_re.tendsto w |>.comp hz)
      (hpos.mono (fun _ h => h.2))
  exact ⟨him, hre⟩

/-- Passing to the joint net uses only finitely many monomial moments for
each fixed p,q. No uniform bound on the renormalization matrices is assumed. -/
theorem reflectionPair_polynomial_tendsto
    {ι σ : Type*} {l : Filter ι}
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (θ : (i : ι) → X i → X i) (hθ : ∀ i, Measurable (θ i))
    (S : (i : ι) → Subalgebra ℂ (X i → ℂ))
    (hreg : ∀ i, BoundedMeasurableAlgebra (S i))
    (R : (i : ι) → σ → X i → ℂ)
    (hR : ∀ᶠ i in l, ∀ a, R i a ∈ S i)
    (C : (σ →₀ ℕ) → (σ →₀ ℕ) → ℂ)
    (hmom : ∀ d e, Tendsto
      (fun i => reflectionPair (μ i) (θ i)
        (monomialField (R i) d) (monomialField (R i) e)) l (𝓝 (C d e)))
    (p q : MvPolynomial σ ℂ) :
    Tendsto (fun i => reflectionPair (μ i) (θ i)
      (polynomialField (R i) p) (polynomialField (R i) q)) l
      (𝓝 (continuumReflectionPair C p q)) := by
  have hsum : Tendsto
      (fun i => ∑ d ∈ p.support, ∑ e ∈ q.support,
        (conj (p.coeff d) * q.coeff e) *
          reflectionPair (μ i) (θ i)
            (monomialField (R i) d) (monomialField (R i) e)) l
      (𝓝 (continuumReflectionPair C p q)) := by
    exact tendsto_finsetSum _ (fun d _ =>
      tendsto_finsetSum _ (fun e _ => (hmom d e).const_mul _))
  apply hsum.congr'
  filter_upwards [hR] with i hi
  exact (reflectionPair_polynomial_expansion
    (μ i) (θ i) (hθ i) (S i) (hreg i) (R i) hi p q).symm

/-- Original #28 / paper Theorem 17.3. Finite-cutoff reflection positivity is
assumed ONLY on the original bounded positive-time algebra. The raw roots'
eventual positive-time support, the defining source mixing, and the SAME
joint monomial moments are explicit. Polynomial positivity at the continuum
is an output; I7, a continuum positive cone, and a uniform mixing bound are
not inputs. Cutoff configuration spaces and raw family sizes may vary. -/
theorem original28_renormalized_continuum_reflection_positivity
    {ι σ : Type*} {l : Filter ι} [l.NeBot]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {τ : ι → Type*} [∀ i, Fintype (τ i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (θ : (i : ι) → X i → X i) (hθ : ∀ i, Measurable (θ i))
    (S : (i : ι) → Subalgebra ℂ (X i → ℂ))
    (hreg : ∀ i, BoundedMeasurableAlgebra (S i))
    (hcutoffRP : ∀ i F, F ∈ S i →
      ComplexNonnegative (reflectionPair (μ i) (θ i) F F))
    (O : (i : ι) → τ i → X i → ℂ)
    (B : (i : ι) → τ i → σ → ℂ)
    (hsupport : ∀ᶠ i in l, ∀ e, O i e ∈ S i)
    (C : (σ →₀ ℕ) → (σ →₀ ℕ) → ℂ)
    (hmom : ∀ d e, Tendsto
      (fun i => reflectionPair (μ i) (θ i)
        (monomialField (mixedField (O i) (B i)) d)
        (monomialField (mixedField (O i) (B i)) e)) l (𝓝 (C d e))) :
    (∀ p q : MvPolynomial σ ℂ,
      Tendsto (fun i => reflectionPair (μ i) (θ i)
        (polynomialField (mixedField (O i) (B i)) p)
        (polynomialField (mixedField (O i) (B i)) q)) l
        (𝓝 (continuumReflectionPair C p q))) ∧
    (∀ p : MvPolynomial σ ℂ,
      ComplexNonnegative (continuumReflectionPair C p p)) ∧
    (∀ p q : MvPolynomial σ ℂ, ∀ᶠ i in l,
      Integrable (fun x =>
        conj (polynomialField (mixedField (O i) (B i)) p (θ i x)) *
          polynomialField (mixedField (O i) (B i)) q x) (μ i)) := by
  have hR : ∀ᶠ i in l, ∀ a, mixedField (O i) (B i) a ∈ S i := by
    filter_upwards [hsupport] with i hi
    exact mixedField_mem (S i) (O i) (B i) hi
  have hlimit (p q : MvPolynomial σ ℂ) :=
    reflectionPair_polynomial_tendsto μ θ hθ S hreg
      (fun i => mixedField (O i) (B i)) hR C hmom p q
  refine ⟨hlimit, ?_, ?_⟩
  · intro p
    apply complexNonnegative_of_tendsto (hlimit p p)
    filter_upwards [hsupport] with i hi
    exact cutoff_polynomial_reflection_positive
      (μ i) (θ i) (S i) (hcutoffRP i) (O i) (B i) hi p
  · intro p q
    filter_upwards [hR] with i hi
    exact reflection_product_integrable (μ i) (θ i) (hθ i) (S i) (hreg i)
      (polynomialField_mem (S i) _ hi p) (polynomialField_mem (S i) _ hi q)

#print axioms original28_renormalized_continuum_reflection_positivity
end YMUIC.Reflection
