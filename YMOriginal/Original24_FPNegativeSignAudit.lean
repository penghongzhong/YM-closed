import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import YMOriginal.Original24_ExactRealTwoRootFPSeries

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# The original two-root FP criterion NEEDS a sign admissibility assumption

The currently unproved PhysicalExactTwoRootFPCriterion is stated for
arbitrary cGeo,mu in R, and the LHS is an UNWEIGHTED positive tree
coefficient while the augmented KP model on the RHS uses
exp(cGeo*mu*d) at every vertex. This is too strong if
cGeo*mu -> -infinity while physical d>0.

A minimal two-species (bulk,q), one-root (p) scalar KP tree already
exhibits the mathematical obstruction. Here both bulk and q have
weighted fugacity eta=1/16, all contacts allowed, and tree recursion

  H_0=1, H_(h+1)=exp(2eta H_h),
  F_h=2eta H_h.

The true unweighted p-bulk-q Mayer tree has coefficient 1.
But exp(F_3)-1 < 1, proved with EXACT real inequalities below,
not floating-point numerics.

This theorem audits the UNIVERSAL CLAIM. The exact physical
finite N=1 periodic-graph-to-scalar equivalence is a separate
source-model dictionary and must not be reported as kernel-checked
by merely proving this scalar obstruction.
-/

/-- Two equally weighted, mutually contacting non-root polymer types. -/
private def twoSpeciesKP (η : ℝ) : ℕ → ℝ
  | 0 => 1
  | h + 1 => Real.exp (2 * η * twoSpeciesKP η h)

/-- Rigorous rational exponential barrier, no approximate arithmetic. -/
private theorem exp_quarter_strict_lt_two :
    Real.exp ((1 : ℝ) / 4) < 2 := by
  have hPow : (Real.exp ((1 : ℝ) / 4)) ^ (4 : ℕ) =
      Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  by_contra h
  have hge : (2 : ℝ) ≤ Real.exp ((1 : ℝ) / 4) :=
    le_of_not_gt h
  have hpowle :
      (2 : ℝ) ^ (4 : ℕ) ≤
        (Real.exp ((1 : ℝ) / 4)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hge _
  nlinarith [Real.exp_one_lt_three]

/-- Every finite generation in the tiny two-species KP recursion
is uniformly at most 2; no FP enumeration is used. -/
private theorem twoSpeciesKP_quarter_bound :
    ∀ h : ℕ, twoSpeciesKP ((1 : ℝ) / 16) h ≤ 2 := by
  intro h
  induction h with
  | zero =>
      change (1 : ℝ) ≤ 2
      norm_num
  | succ h ih =>
      change Real.exp (2 * ((1 : ℝ) / 16) *
        twoSpeciesKP ((1 : ℝ) / 16) h) ≤ 2
      calc
        Real.exp (2 * ((1 : ℝ) / 16) *
            twoSpeciesKP ((1 : ℝ) / 16) h) ≤
          Real.exp ((1 : ℝ) / 4) := by
            apply Real.exp_le_exp.mpr
            nlinarith [ih]
        _ < 2 := exp_quarter_strict_lt_two

/-- Strictly positive UNWEIGHTED one-bulk p-X-q tree coefficient 1
is NOT dominated by the two-species KP RHS after a large negative
geometric exponent. This is a genuine contradiction to a statement
that omits the necessary sign/weight comparison assumption. -/
theorem original24_FP_negative_geom_scalar_obstruction :
    (1 : ℝ) >
      Real.exp (2 * ((1 : ℝ) / 16) *
        twoSpeciesKP ((1 : ℝ) / 16) 3) - 1 := by
  have hH := twoSpeciesKP_quarter_bound 3
  have hBound :
      2 * ((1 : ℝ) / 16) *
        twoSpeciesKP ((1 : ℝ) / 16) 3 ≤ (1 : ℝ) / 4 := by
    nlinarith [hH]
  have he : Real.exp
      (2 * ((1 : ℝ) / 16) *
        twoSpeciesKP ((1 : ℝ) / 16) 3) ≤
        Real.exp ((1 : ℝ) / 4) :=
    Real.exp_le_exp.mpr hBound
  linarith [exp_quarter_strict_lt_two]

/-- The negative geometric exponent producing eta=1/16 is a
FINITE admissible real number, not an asymptotic formal symbol. -/
theorem original24_FP_negative_geom_finite_parameter :
    ∃ cGeo mu : ℝ, cGeo * mu < 0 ∧
      Real.exp (cGeo * mu * (1 : ℝ)) = (1 : ℝ) / 16 := by
  refine ⟨Real.log ((1 : ℝ) / 16), 1, ?_, ?_⟩
  · simpa only [mul_one] using
      (Real.log_neg (by norm_num : (0 : ℝ) < 1 / 16)
        (by norm_num : (1 : ℝ) / 16 < 1))
  · simpa only [mul_one] using
      (Real.exp_log (by norm_num : (0 : ℝ) < 1 / 16))

end YMUIC.Original24
