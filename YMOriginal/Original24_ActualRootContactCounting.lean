import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# C29 U2: root-neighborhood counting with REAL finite block supports

The upstream proof used abstract root-tree totals as assumptions.
Here the key U2 first-attachment counting is constructed from actual
FINITE block supports and their contact neighborhoods.

For a root support R in a 4D finite block lattice B, with finite
contact neighborhood N(b), define:
  A(R)=Union_{b∈R} N(b)
  C(R)={polymers X: support(X) intersects A(R)}
  T(Delta)={polymers X: Delta∈support(X)}.
We prove the covering relation C(R)⊆Union_{Delta∈A(R)}T(Delta),
|A(R)|≤Nchi*|R|, and the root activity bound

  Sum_{X∈C(R)} w(X) <= Nchi*|R|*aAct,

assuming only the ORIGINAL unrooted per-block activity norm
  sup_Delta Sum_{X∋Delta} w(X) <= aAct.

No bound on the marked/root-contact sum is a hypothesis.
No polymer tree enumeration or physical RG uniform norm is proven
here: the actual U1 per-block norm and full two-root FP enumeration
remain model/external inputs.
-/

/-- The exact union of all physical contact neighborhoods of the
finite lattice blocks touched by the external Wilson root. -/
def actualRootNeighbourhood
    {Block : Type*} [DecidableEq Block]
    (root : Finset Block) (neighbors : Block → Finset Block) :
    Finset Block :=
  root.biUnion neighbors

/-- All polymer species covering the physical block Delta. -/
def actualThroughBlock
    {Block Γ : Type*} [DecidableEq Block] [Fintype Γ]
    (support : Γ → Finset Block) (Delta : Block) : Finset Γ := by
  classical
  exact Finset.univ.filter (fun X => Delta ∈ support X)

/-- The finite family of polymers truly contacting a finite supported
Wilson root. No arbitrary root-attachment relation is introduced. -/
def actualContactRoot
    {Block Γ : Type*} [DecidableEq Block] [Fintype Γ]
    (root : Finset Block) (neighbors : Block → Finset Block)
    (support : Γ → Finset Block) : Finset Γ := by
  classical
  exact Finset.univ.filter (fun X =>
    ∃ Delta ∈ actualRootNeighbourhood root neighbors,
      Delta ∈ support X)

/-- The actual contact condition implies the exact block covering
premise of the original U2 first-root counting theorem. -/
theorem actual_root_contact_covered
    {Block Γ : Type*} [DecidableEq Block] [Fintype Γ]
    (root : Finset Block) (neighbors : Block → Finset Block)
    (support : Γ → Finset Block) :
    ∀ X ∈ actualContactRoot root neighbors support,
      ∃ Delta ∈ actualRootNeighbourhood root neighbors,
        X ∈ actualThroughBlock support Delta := by
  classical
  intro X hX
  simp only [actualContactRoot, Finset.mem_filter,
    Finset.mem_univ, true_and] at hX
  obtain ⟨Delta,hDelta,hSupp⟩ := hX
  exact ⟨Delta,hDelta,by simp [actualThroughBlock,hSupp]⟩

/-- Physical root neighborhood cardinality has NO bulk-placement
factor: it is bounded solely by support size and local coordination. -/
theorem actual_root_neighborhood_card_le
    {Block : Type*} [DecidableEq Block]
    (root : Finset Block) (neighbors : Block → Finset Block)
    (Nchi : ℕ)
    (hlocal : ∀ Delta ∈ root, (neighbors Delta).card ≤ Nchi) :
    (actualRootNeighbourhood root neighbors).card ≤
      Nchi * root.card := by
  unfold actualRootNeighbourhood
  calc
    (root.biUnion neighbors).card ≤
      ∑ Delta ∈ root, (neighbors Delta).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _Delta ∈ root, Nchi := by
      apply Finset.sum_le_sum
      intro Delta hDelta
      exact hlocal Delta hDelta
    _ = Nchi * root.card := by simp [Nat.mul_comm]

/-- Actual finite root-contact sum is bounded by the UNMARKED
per-block polymer norm and genuine contact-block counting.
There is no input hypothesis that presupposes the desired
rooted or marked conclusion. -/
theorem actual_root_contact_sum_from_block_norm
    {Block Γ : Type*} [DecidableEq Block] [Fintype Γ]
    (root : Finset Block) (neighbors : Block → Finset Block)
    (support : Γ → Finset Block)
    (weight : Γ → ℝ) (aAct : ℝ) (Nchi : ℕ)
    (hweight : ∀ X, 0 ≤ weight X)
    (haAct : 0 ≤ aAct)
    (hlocalN : ∀ Delta ∈ root, (neighbors Delta).card ≤ Nchi)
    (hLocalNorm : ∀ Delta,
      (∑ X ∈ actualThroughBlock support Delta, weight X) ≤ aAct) :
    (∑ X ∈ actualContactRoot root neighbors support, weight X) ≤
      ((Nchi : ℝ) * (root.card : ℝ)) * aAct := by
  let A := actualRootNeighbourhood root neighbors
  let C := actualContactRoot root neighbors support
  let T := actualThroughBlock support
  have hcover :
      ∀ X ∈ C, ∃ Delta ∈ A, X ∈ T Delta :=
    actual_root_contact_covered root neighbors support
  have hdouble :
      (∑ X ∈ C, weight X) ≤
        ∑ Delta ∈ A, ∑ X ∈ T Delta, weight X := by
    classical
    calc
      (∑ X ∈ C, weight X) ≤
          ∑ X ∈ C,
            ∑ Delta ∈ A, if X ∈ T Delta then weight X else 0 := by
        apply Finset.sum_le_sum
        intro X hX
        obtain ⟨Delta,hDelta,hIn⟩ := hcover X hX
        have hnonneg :
            ∀ Delta' ∈ A,
              0 ≤ if X ∈ T Delta' then weight X else 0 := by
          intro Delta' _
          split_ifs <;> positivity
        have h := Finset.single_le_sum hnonneg hDelta
        simpa [hIn] using h
      _ ≤ ∑ X ∈ (Finset.univ : Finset Γ),
            ∑ Delta ∈ A, if X ∈ T Delta then weight X else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ _
        · intro X _ _
          apply Finset.sum_nonneg
          intro Delta _
          split_ifs <;> positivity
      _ = ∑ Delta ∈ A, ∑ X ∈ T Delta, weight X := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Delta _
        simp
  have hcard := actual_root_neighborhood_card_le
    root neighbors Nchi hlocalN
  have hcardR :
      (A.card : ℝ) ≤ (Nchi : ℝ) * (root.card : ℝ) := by
    exact_mod_cast hcard
  calc
    (∑ X ∈ actualContactRoot root neighbors support, weight X) ≤
      ∑ Delta ∈ A, ∑ X ∈ T Delta, weight X := hdouble
    _ ≤ ∑ _Delta ∈ A, aAct := by
      apply Finset.sum_le_sum
      intro Delta _
      exact hLocalNorm Delta
    _ = (A.card : ℝ) * aAct := by simp [nsmul_eq_mul]
    _ ≤ ((Nchi : ℝ) * (root.card : ℝ)) * aAct :=
      mul_le_mul_of_nonneg_right hcardR haAct

end YMUIC.Original24
