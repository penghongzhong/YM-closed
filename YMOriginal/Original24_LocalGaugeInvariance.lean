import YMOriginal.Original24_WilsonWordPolynomial

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Exact local SU(2) gauge conjugacy of all fixed Wilson-word polynomials

Under a shared-basepoint lattice gauge transformation g∈SU(2),
each plaquette holonomy U_p becomes g U_p g^{-1}.
Ordered Wilson words transform by the same conjugation, their
traces remain equal, and every finite product/polynomial of the
actual word roots is gauge invariant.

No physical gauge-fixing, source normalization or RG model bound is
assumed. This proves a genuine *local algebraic gauge-invariance*
component of the Original24 fixed-template source dictionary.
-/

private abbrev SU2Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- Matrix trace is invariant under a single SU(2) conjugation. -/
theorem wilson_root_conjugation_invariant
    (g u : SU2) :
    wilsonRoot (g * u * g⁻¹) = wilsonRoot u := by
  have hginv :
      ((g⁻¹ : SU2) : SU2Mat) * (g : SU2Mat) = 1 := by
    change (((g⁻¹ * g : SU2) : SU2Mat) = 1)
    simp
  have ht :
      Matrix.trace (((g * u * g⁻¹ : SU2) : SU2Mat)) =
        Matrix.trace (u : SU2Mat) := by
    change Matrix.trace (((g : SU2Mat) * (u : SU2Mat)) *
      ((g⁻¹ : SU2) : SU2Mat)) = Matrix.trace (u : SU2Mat)
    calc
      _ = Matrix.trace (((g⁻¹ : SU2) : SU2Mat) *
          ((g : SU2Mat) * (u : SU2Mat))) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((((g⁻¹ : SU2) : SU2Mat) * (g : SU2Mat)) *
          (u : SU2Mat)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (u : SU2Mat) := by rw [hginv, one_mul]
  change 2 - (Matrix.trace (((g * u * g⁻¹ : SU2) : SU2Mat))).re =
    2 - (Matrix.trace (u : SU2Mat)).re
  rw [ht]

/-- Correct chronological SU(2) ordered word holonomy transforms
by simultaneous basepoint gauge conjugation. -/
theorem wilson_word_holonomy_conjugation
    {P : Type*} (g : SU2) (U : P → SU2) (w : List P) :
    wilsonWordHolonomy (fun p => g * U p * g⁻¹) w =
      g * wilsonWordHolonomy U w * g⁻¹ := by
  induction w with
  | nil =>
      simp [wilsonWordHolonomy]
  | cons p rest ih =>
      simp only [wilsonWordHolonomy, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]
      group

theorem wilson_word_root_conjugation_invariant
    {P : Type*} (g : SU2) (U : P → SU2) (w : List P) :
    wilsonWordRoot (fun p => g * U p * g⁻¹) w =
      wilsonWordRoot U w := by
  unfold wilsonWordRoot
  rw [wilson_word_holonomy_conjugation]
  exact wilson_root_conjugation_invariant _ _

theorem actual_wilson_monomial_gauge_invariant
    {P : Type*} (g : SU2) (U : P → SU2)
    (words : List (List P)) :
    actualWilsonMonomial (fun p => g * U p * g⁻¹) words =
      actualWilsonMonomial U words := by
  induction words with
  | nil => rfl
  | cons w rest ih =>
      simp only [actualWilsonMonomial]
      rw [wilson_word_root_conjugation_invariant, ih]

theorem actual_wilson_polynomial_gauge_invariant
    {P T : Type*} [Fintype T]
    (g : SU2) (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ) :
    actualWilsonPolynomial (fun p => g * U p * g⁻¹) words coeff =
      actualWilsonPolynomial U words coeff := by
  unfold actualWilsonPolynomial
  apply Finset.sum_congr rfl
  intro t ht
  rw [actual_wilson_monomial_gauge_invariant]

#print axioms actual_wilson_polynomial_gauge_invariant

end YMUIC.Original24
