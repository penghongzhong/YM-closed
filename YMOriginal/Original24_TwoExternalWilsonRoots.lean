import YMOriginal.Original24_ActualLatticeLinks
import YMOriginal.Original24_FromU1U2B10

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Exact C29 Lemma 15.4: two ACTUAL SU2 composite external roots

The C29 original bounded-external-root lemma has TWO roots p,q,
with independent complex source variables s,t, not just the one-root
marked post-R activity. We implement both as actual finite-complexity
SU2 Wilson-word polynomials. Their connected rooted insertion is
the product (exp(s O_p)-1)(exp(t O_q)-1), with exact mixed-source
subtraction, and it is multiplied against the UNMODIFIED bulk
old/new-R activity.

The analysis uses the original U1 old/new unmarked activity bounds,
the exact geometric root-distance dictionary, and the U2 rooted-tree
sum, all explicit model inputs. There is NO premise of
R_j(s,t) composite-source analyticity or of a marked-R bound.
The fixed-D normalized jet and actual CMP119/122 polymer identities
remain model-specific obligations. This file alone is NOT
a full original-environment #24 certificate.
-/

/-- Two independent source parameters and finite actual SU2 Wilson
word polynomial roots, without deforming the bulk R-operation. -/
def actualTwoRootInsertion
    {P T S : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) : ℂ :=
  actualWilsonInsertion U wp cp s *
    actualWilsonInsertion U wq cq t

/-- The exact mixed external-source subtraction identity:
one root at p and one at q, with no one-root disconnected part. -/
theorem actual_two_root_mixed_subtraction
    {P T S : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) :
    actualTwoRootInsertion U wp cp wq cq s t =
      Complex.exp
        (s * actualWilsonPolynomial U wp cp +
          t * actualWilsonPolynomial U wq cq) -
      Complex.exp (s * actualWilsonPolynomial U wp cp) -
      Complex.exp (t * actualWilsonPolynomial U wq cq) + 1 := by
  unfold actualTwoRootInsertion actualWilsonInsertion
  rw [Complex.exp_add]
  ring

/-- Exact two-root source bound from genuine SU2 Wilson polynomial
amplitudes; source smallness is checked separately at p and q. -/
theorem actual_two_root_insertion_small
    {P T S : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ)
    (hp : ‖s‖ * actualWilsonPolynomialBudget wp cp ≤ 1)
    (hq : ‖t‖ * actualWilsonPolynomialBudget wq cq ≤ 1) :
    ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤
      (2 * ‖s‖ * actualWilsonPolynomialBudget wp cp) *
      (2 * ‖t‖ * actualWilsonPolynomialBudget wq cq) := by
  change ‖actualWilsonInsertion U wp cp s *
    actualWilsonInsertion U wq cq t‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul
    (actual_wilson_insertion_bound U wp cp s hp)
    (actual_wilson_insertion_bound U wq cq t hq)
    (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (actual_wilson_polynomial_budget_nonneg wp cp))

/-- The actual second-order rooted history multiplier is the exact
mixed insertion times the unchanged unmarked polymer activity. -/
def actualTwoRootMarkedR
    {P T S Γ : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (unmarked : Γ → ℂ) (γ : Γ) : ℂ :=
  actualTwoRootInsertion U wp cp wq cq s t * unmarked γ

/-- The connected two-external-root U2 rooted-tree estimate,
with the root cost paid exactly TWICE (not in bulk placement entropy).
The physical exponential tree data are U2 hypotheses only. -/
theorem actual_two_root_marked_tree_sum
    {P T S Γ : Type*} [Fintype T] [Fintype S]
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ)
    (hp : ‖s‖ * actualWilsonPolynomialBudget wp cp ≤ 1)
    (hq : ‖t‖ * actualWilsonPolynomialBudget wq cq ≤ 1)
    (unmarked : Γ → ℂ) (treeWeight : Γ → ℝ)
    (mu cRt dRoot aAct : ℝ) (Nroot : ℕ)
    (htree : ∀ γ, 0 ≤ treeWeight γ)
    (hweighted : ∀ γ,
      Real.exp (mu * dRoot) * ‖unmarked γ‖ ≤
        Real.exp (mu * cRt) * treeWeight γ)
    (hsum : Summable treeWeight)
    (htotal : (∑' γ, treeWeight γ) ≤ (Nroot : ℝ) * aAct) :
    (∑' γ, ‖actualTwoRootMarkedR U wp cp wq cq s t
      unmarked γ‖) ≤
      ((2 * ‖s‖ * actualWilsonPolynomialBudget wp cp) *
        (2 * ‖t‖ * actualWilsonPolynomialBudget wq cq)) *
      Real.exp (mu * cRt) * (Nroot : ℝ) *
      aAct * Real.exp (-mu * dRoot) := by
  let K : ℝ :=
    (2 * ‖s‖ * actualWilsonPolynomialBudget wp cp) *
      (2 * ‖t‖ * actualWilsonPolynomialBudget wq cq)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hp0 := actual_wilson_polynomial_budget_nonneg wp cp
    have hq0 := actual_wilson_polynomial_budget_nonneg wq cq
    positivity
  have hD : ‖actualTwoRootInsertion U wp cp wq cq s t‖ ≤ K :=
    actual_two_root_insertion_small U wp cp wq cq s t hp hq
  have hw (γ : Γ) :
      Real.exp (mu * dRoot) *
        ‖actualTwoRootMarkedR U wp cp wq cq s t unmarked γ‖ ≤
          K * Real.exp (mu * cRt) * treeWeight γ := by
    calc
      Real.exp (mu * dRoot) *
        ‖actualTwoRootMarkedR U wp cp wq cq s t unmarked γ‖ =
          ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
            (Real.exp (mu * dRoot) * ‖unmarked γ‖) := by
              simp only [actualTwoRootMarkedR, norm_mul]
              ring
      _ ≤ ‖actualTwoRootInsertion U wp cp wq cq s t‖ *
          (Real.exp (mu * cRt) * treeWeight γ) :=
            mul_le_mul_of_nonneg_left (hweighted γ) (norm_nonneg _)
      _ ≤ K * (Real.exp (mu * cRt) * treeWeight γ) :=
            mul_le_mul_of_nonneg_right hD
              (mul_nonneg (Real.exp_pos _).le (htree γ))
      _ = K * Real.exp (mu * cRt) * treeWeight γ := by ring
  exact one_root_tree_sum
    (fun γ => ‖actualTwoRootMarkedR U wp cp wq cq s t unmarked γ‖)
    treeWeight K mu cRt dRoot aAct Nroot
    (fun γ => norm_nonneg _) htree hK hw hsum htotal

/-- Exact local lattice polynomial of closed SU2 link Wilson loops,
with two independent source directions, is invariant under every
independent vertex gauge transformation (no gauge-fixing assumed). -/
def actualTwoLinkRootInsertion
    {Vertex T S : Type*} [Fintype T] [Fintype S]
    (base : Vertex) (U : Vertex → Vertex → SU2)
    (wp : T → List (List (ClosedLinkWalkAt Vertex base))) (cp : T → ℂ)
    (wq : S → List (List (ClosedLinkWalkAt Vertex base))) (cq : S → ℂ)
    (s t : ℂ) : ℂ :=
  (Complex.exp (s * actualLinkWilsonPolynomial base U wp cp) - 1) *
    (Complex.exp (t * actualLinkWilsonPolynomial base U wq cq) - 1)

theorem actual_two_link_root_gauge_invariant
    {Vertex T S : Type*} [Fintype T] [Fintype S]
    (base : Vertex) (g : Vertex → SU2) (U : Vertex → Vertex → SU2)
    (wp : T → List (List (ClosedLinkWalkAt Vertex base))) (cp : T → ℂ)
    (wq : S → List (List (ClosedLinkWalkAt Vertex base))) (cq : S → ℂ)
    (s t : ℂ) :
    actualTwoLinkRootInsertion base (transformedLink g U) wp cp wq cq s t =
      actualTwoLinkRootInsertion base U wp cp wq cq s t := by
  simp only [actualTwoLinkRootInsertion,
    actual_link_wilson_polynomial_gauge_invariant]

end YMUIC.Original24
