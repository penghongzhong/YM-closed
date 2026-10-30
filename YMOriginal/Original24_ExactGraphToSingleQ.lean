import YMOriginal.Original24_ExactAugmentedQContact
import YMOriginal.Original24_UniqueQFactorial
import YMOriginal.Original24_ExactExtendedTwoRootMayer
import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
The original C29 Mayer graph has n labeled bulk vertices and
two external source roots p,q.  Here q is relabeled as ONE augmented
physical polymer species, while p remains the unique rooted source.

The graph comparison preserves the same actual periodic supports,
bulk-bulk hard-core contact and bulk-q contact.  The augmented model
may contain an EXTRA p-q edge; we need only a subgraph inclusion,
not an invalid equality.  No FP tree enumeration is assumed here.
-/

/-- Exact bijection: bulk labels stay bulk, q becomes a special polymer,
and p remains the first external root. -/
def twoRootToSingleQ (n : ℕ) :
    Sum (Fin n) (Fin 2) ≃ Sum (Sum (Fin n) Unit) Unit where
  toFun
    | Sum.inl i => Sum.inl (Sum.inl i)
    | Sum.inr k =>
        if k = 0 then Sum.inr () else Sum.inl (Sum.inr ())
  invFun
    | Sum.inl (Sum.inl i) => Sum.inl i
    | Sum.inl (Sum.inr _) => Sum.inr 1
    | Sum.inr _ => Sum.inr 0
  left_inv := by
    intro x
    cases x with
    | inl i => rfl
    | inr k => fin_cases k <;> simp
  right_inv := by
    intro x
    cases x with
    | inl i =>
        cases i with
        | inl j => rfl
        | inr u => cases u; rfl
    | inr u => cases u; rfl

/-- The species of each labeled augmented non-root vertex. -/
def actualSingleQTag {Γ : Type*} {n : ℕ}
    (tuple : Fin n → Γ) : Sum (Fin n) Unit → Sum Γ Unit
  | Sum.inl i => Sum.inl (tuple i)
  | Sum.inr _ => Sum.inr ()

/-- One-root, q-augmented hard-core graph with ACTUAL physical supports.
It keeps an optional direct p-q contact, which only enlarges the
set of spanning trees relative to the original no-p-q-edge graph. -/
def actualSingleQRootRelation
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    Sum (Sum (Fin n) Unit) Unit →
      Sum (Sum (Fin n) Unit) Unit → Prop
  | Sum.inl i, Sum.inl j =>
      actualPeriodicHardCoreIncompatible N chi
        (actualSecondRootAugmentedSupport N support rootQ)
        (actualSingleQTag tuple i) (actualSingleQTag tuple j)
  | Sum.inl i, Sum.inr _ =>
      actualSingleQTag tuple i ∈
        actualContactRoot rootP (fourDimPeriodicNeighborhood N chi)
          (actualSecondRootAugmentedSupport N support rootQ)
  | Sum.inr _, Sum.inl j =>
      actualSingleQTag tuple j ∈
        actualContactRoot rootP (fourDimPeriodicNeighborhood N chi)
          (actualSecondRootAugmentedSupport N support rootQ)
  | Sum.inr _, Sum.inr _ => False

def actualSingleQRootGraph
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    SimpleGraph (Sum (Sum (Fin n) Unit) Unit) :=
  SimpleGraph.fromRel
    (actualSingleQRootRelation n N chi rootP rootQ support tuple)

private theorem bulk_augmented_root_contact_iff
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) (X : Γ) :
    (Sum.inl X : Sum Γ Unit) ∈
      actualContactRoot rootP (fourDimPeriodicNeighborhood N chi)
        (actualSecondRootAugmentedSupport N support rootQ) ↔
    X ∈ actualContactRoot rootP
        (fourDimPeriodicNeighborhood N chi) support := by
  classical
  unfold actualContactRoot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

private theorem bulk_augmented_bulk_incompatible
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) (X Y : Γ)
    (h : actualPeriodicHardCoreIncompatible N chi support X Y) :
    actualPeriodicHardCoreIncompatible N chi
      (actualSecondRootAugmentedSupport N support rootQ)
      (Sum.inl X) (Sum.inl Y) := by
  rcases h with h | h | h
  · exact Or.inl (congrArg Sum.inl h)
  · exact Or.inr (Or.inl
      ((actual_augmented_bulk_children_iff_original
        N chi support rootQ Y X).mpr h))
  · exact Or.inr (Or.inr
      ((actual_augmented_bulk_children_iff_original
        N chi support rootQ X Y).mpr h))

private theorem bulk_augmented_q_incompatible
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) (X : Γ)
    (h : X ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support) :
    actualPeriodicHardCoreIncompatible N chi
      (actualSecondRootAugmentedSupport N support rootQ)
      (Sum.inl X) (Sum.inr ()) := by
  exact Or.inr (Or.inr
    ((actual_augmented_second_root_bulk_contact_iff
      N chi support rootQ X).mpr h))

private theorem q_augmented_bulk_incompatible
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) (X : Γ)
    (h : X ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support) :
    actualPeriodicHardCoreIncompatible N chi
      (actualSecondRootAugmentedSupport N support rootQ)
      (Sum.inr ()) (Sum.inl X) := by
  exact Or.inr (Or.inl
    ((actual_augmented_second_root_bulk_contact_iff
      N chi support rootQ X).mpr h))

/-- Every directed edge of the EXACT original two-root graph becomes
a directed permissible edge of the single-q augmented graph.
No false root-root-edge equality is needed. -/
theorem original24_exact_relation_to_single_q
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ)
    (u v : Sum (Fin n) (Fin 2))
    (h : actualExactTwoRootRelation n N chi rootP rootQ
      support tuple u v) :
    actualSingleQRootRelation n N chi rootP rootQ support tuple
      (twoRootToSingleQ n u) (twoRootToSingleQ n v) := by
  classical
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          exact bulk_augmented_bulk_incompatible N chi rootQ support
            (tuple i) (tuple j) h
      | inr k =>
          fin_cases k
          · exact (bulk_augmented_root_contact_iff
              N chi rootP rootQ support (tuple i)).mpr h
          · exact bulk_augmented_q_incompatible N chi rootQ
              support (tuple i) h
  | inr k =>
      fin_cases k
      · cases v with
        | inl j =>
            exact (bulk_augmented_root_contact_iff
              N chi rootP rootQ support (tuple j)).mpr h
        | inr l =>
            fin_cases l <;> cases h
      · cases v with
        | inl j =>
            exact q_augmented_bulk_incompatible N chi rootQ
              support (tuple j) h
        | inr l =>
            fin_cases l <;> cases h

/-- Core PHYSICAL graph dictionary for original24:
every exact n+2-vertex Mayer edge is preserved by the bijection
to the one-q augmented p-rooted graph, allowing arbitrary q degree.
The implication is at the original hard-core support level, not
a model-free graph or an assumed Mayer majorant. -/
theorem original24_exact_graph_embeds_single_q
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ)
    (u v : Sum (Fin n) (Fin 2))
    (h : (actualExactTwoRootGraph n N chi
      rootP rootQ support tuple).Adj u v) :
    (actualSingleQRootGraph n N chi rootP rootQ support tuple).Adj
      (twoRootToSingleQ n u) (twoRootToSingleQ n v) := by
  have hh :
      u ≠ v ∧
      (actualExactTwoRootRelation n N chi rootP rootQ support tuple u v ∨
       actualExactTwoRootRelation n N chi rootP rootQ support tuple v u) := by
    simpa [actualExactTwoRootGraph, SimpleGraph.fromRel_adj] using h
  change (twoRootToSingleQ n u ≠ twoRootToSingleQ n v) ∧
    (actualSingleQRootRelation n N chi rootP rootQ support tuple
       (twoRootToSingleQ n u) (twoRootToSingleQ n v) ∨
     actualSingleQRootRelation n N chi rootP rootQ support tuple
       (twoRootToSingleQ n v) (twoRootToSingleQ n u))
  refine ⟨?_, ?_⟩
  · intro e
    exact hh.1 ((twoRootToSingleQ n).injective e)
  · rcases hh.2 with he | he
    · exact Or.inl (original24_exact_relation_to_single_q
        n N chi rootP rootQ support tuple u v he)
    · exact Or.inr (original24_exact_relation_to_single_q
        n N chi rootP rootQ support tuple v u he)

end YMUIC.Original24
