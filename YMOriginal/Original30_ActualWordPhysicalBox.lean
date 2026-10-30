import YMOriginal.Original30_ActualWordSmearing
import YM.Wilson.FixedBoxSmearing

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# Actual four-dimensional periodic Wilson-word polynomial source cubature

The source contains 6*N^4 physical plaquettes, each with its REAL
physical a^4 lattice weight. For N*a<=R, the exact finite source sum
is independent of N and of the UV cutoff, for arbitrary finite
noncommutative SU2 Wilson-word polynomial templates with an explicit
fixed-template coefficient budget K.

No assumption about the sum of lattice weights is introduced:
the 6*R^4 cubature bound is DERIVED from real plaquette cardinality.
No claim is made for unbounded R, or that a^-d renormalized/composite
counterterm coefficients have a uniform K; such source normalization
must be proved from the actual RG and geometry.
-/

/-- Source of actual finite SU(2) Wilson-word polynomials on the full
physical N^4 periodic hypercube, with 6 positive plaquette directions. -/
theorem actual_word_box_smearing_bound
    {W T : Type*} [Fintype T]
    (N : ℕ) (a R : ℝ)
    (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hbox : (N : ℝ) * a ≤ R)
    (U : WilsonBoxPlaquettes N → W → SU2)
    (position : WilsonBoxPlaquettes N → Space4)
    (words : WilsonBoxPlaquettes N → T → List (List W))
    (coeff : WilsonBoxPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p, actualWilsonPolynomialBudget
      (words p) (coeff p) ≤ K)
    (f : SchwartzMap Space4 ℂ) (q : ℕ) :
    ‖actualWordSchwartzSmearing
      (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      position U words coeff f‖ ≤
      6 * K * R ^ 4 *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ q 0 f) := by
  have hC : 0 ≤ 6 * R ^ 4 := by positivity
  have hW := actual_word_schwartz_smearing_bound
    (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    position U words coeff f q K (6 * R ^ 4) hK hC
    hbudget
    (wilson_box_weighted_sum_bound
      N a R ha hR hbox position q)
  convert hW using 1
  ring

/-- The same true box-size bound holds simultaneously for every cutoff
and lattice volume with N*a<=R, without identifying distinct cutoff
configuration spaces or physical Hilbert spaces. -/
theorem actual_word_box_smearing_all_regulators
    {Regulator W T : Type*} [Fintype T]
    (N : Regulator → ℕ) (a : Regulator → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ i, 0 ≤ a i)
    (hbox : ∀ i, (N i : ℝ) * a i ≤ R)
    (U : ∀ i, WilsonBoxPlaquettes (N i) → W → SU2)
    (position : ∀ i, WilsonBoxPlaquettes (N i) → Space4)
    (words : ∀ i, WilsonBoxPlaquettes (N i) → T → List (List W))
    (coeff : ∀ i, WilsonBoxPlaquettes (N i) → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ i (p : WilsonBoxPlaquettes (N i)),
      actualWilsonPolynomialBudget (words i p) (coeff i p) ≤ K)
    (f : SchwartzMap Space4 ℂ) (q : ℕ) :
    ∀ i, ‖actualWordSchwartzSmearing
      (fun _ : WilsonBoxPlaquettes (N i) =>
        (((a i) ^ 4 : ℝ) : ℂ))
      (position i) (U i) (words i) (coeff i) f‖ ≤
      6 * K * R ^ 4 *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ q 0 f) := by
  intro i
  exact actual_word_box_smearing_bound
    (N i) (a i) R (ha i) hR (hbox i) (U i)
    (position i) (words i) (coeff i) K hK (hbudget i) f q

end YMUIC.Original30
