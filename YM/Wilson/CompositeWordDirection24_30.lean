import YM.Wilson.CompositeWordPolynomial24

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Physical finite-volume composite Wilson Schwartz source dictionary

For a single genuine SU(2) link/plaquette configuration U shared by
all source sites p, each root is a finite polynomial of noncommuting
ordered Wilson-word traces.  The entire finite source vector J_U(f)
is bounded in ℓ∞ by the REAL Schwartz p_{0,0} seminorm with no volume
factor.  This verifies the concrete bare-source half of the 24/30
dictionary; renormalized coefficients and C² Fourier localization
remain external model obligations.
-/

/-- Finite-volume actual SU(2) composite Wilson source vector. -/
def compositeWilsonDirection
    {P Q T : Type*} [Fintype P] [Fintype T]
    (U : Q → SU2)
    (monomials : P → T → List (List Q))
    (coeff : P → T → ℂ)
    (position : P → Space4)
    (f : SchwartzMap Space4 ℂ) : P → ℂ :=
  fun p => wilsonWordPolynomialSchwartzSource U
    (monomials p) (coeff p) (position p) f

/-- The full source vector has no factor |P|, and requires only
an explicit fixed-template coefficient budget at each source site. -/
theorem composite_wilson_direction_uniform
    {P Q T : Type*} [Fintype P] [Fintype T]
    (U : Q → SU2)
    (monomials : P → T → List (List Q))
    (coeff : P → T → ℂ)
    (position : P → Space4)
    (f : SchwartzMap Space4 ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ p,
      wilsonWordPolynomialBudget (monomials p) (coeff p) ≤ B) :
    ‖compositeWilsonDirection U monomials coeff position f‖ ≤
      B * SchwartzMap.seminorm ℂ 0 0 f := by
  have hnonneg : 0 ≤ B * SchwartzMap.seminorm ℂ 0 0 f :=
    mul_nonneg hB (apply_nonneg _ _)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro p
  calc
    ‖compositeWilsonDirection U monomials coeff position f p‖ ≤
        wilsonWordPolynomialBudget (monomials p) (coeff p) *
          SchwartzMap.seminorm ℂ 0 0 f :=
      wilson_word_polynomial_schwartz_bound
        U (monomials p) (coeff p) (position p) f
    _ ≤ B * SchwartzMap.seminorm ℂ 0 0 f :=
      mul_le_mul_of_nonneg_right
        (hbudget p) (apply_nonneg _ _)

/-- Actual source directions are exactly complex linear in the test. -/
theorem composite_wilson_direction_sub
    {P Q T : Type*} [Fintype P] [Fintype T]
    (U : Q → SU2)
    (monomials : P → T → List (List Q))
    (coeff : P → T → ℂ)
    (position : P → Space4)
    (f g : SchwartzMap Space4 ℂ) :
    compositeWilsonDirection U monomials coeff position (f - g) =
      compositeWilsonDirection U monomials coeff position f -
      compositeWilsonDirection U monomials coeff position g := by
  funext p
  change (f (position p) - g (position p)) *
        wilsonWordPolynomial U (monomials p) (coeff p) =
      f (position p) * wilsonWordPolynomial U (monomials p) (coeff p) -
        g (position p) * wilsonWordPolynomial U (monomials p) (coeff p)
  ring

/-- Uniform Lipschitz continuity in the actual bare Wilson source vector. -/
theorem composite_wilson_direction_lipschitz
    {P Q T : Type*} [Fintype P] [Fintype T]
    (U : Q → SU2)
    (monomials : P → T → List (List Q))
    (coeff : P → T → ℂ)
    (position : P → Space4)
    (f g : SchwartzMap Space4 ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ p,
      wilsonWordPolynomialBudget (monomials p) (coeff p) ≤ B) :
    ‖compositeWilsonDirection U monomials coeff position f -
        compositeWilsonDirection U monomials coeff position g‖ ≤
      B * SchwartzMap.seminorm ℂ 0 0 (f - g) := by
  rw [← composite_wilson_direction_sub]
  exact composite_wilson_direction_uniform
    U monomials coeff position (f - g) B hB hbudget

/-- All cutoffs and volumes: the same B controls genuine composite
SU(2) Wilson source directions on regulator-dependent source sites. -/
theorem composite_wilson_direction_all_regulators
    {Regulator T : Type*} [Fintype T]
    (P Q : Regulator → Type*) [∀ a, Fintype (P a)]
    (U : (a : Regulator) → Q a → SU2)
    (monomials : (a : Regulator) → P a → T → List (List (Q a)))
    (coeff : (a : Regulator) → P a → T → ℂ)
    (position : (a : Regulator) → P a → Space4)
    (f : SchwartzMap Space4 ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ a p,
      wilsonWordPolynomialBudget (monomials a p) (coeff a p) ≤ B) :
    ∀ a, ‖compositeWilsonDirection (U a)
        (monomials a) (coeff a) (position a) f‖ ≤
      B * SchwartzMap.seminorm ℂ 0 0 f := by
  intro a
  exact composite_wilson_direction_uniform
    (U a) (monomials a) (coeff a) (position a) f B hB
    (hbudget a)

end YMUIC.Wilson
