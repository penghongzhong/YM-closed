import YMOriginal.Original24_PeriodicHardCoreEquivalence
import YMOriginal.Original24_AugmentedSecondRootKP
import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Original24: exact second-root-as-polymer physical adjacency dictionary

The corrected one-q augmented U2/KP model adjoins
  Sum.inr () : Sum Γ Unit
as ONE physical second Wilson-root polymer species.
The old n+2 extended graph has the *second external root* q,
and a root-to-bulk edge iff the bulk support meets the actual
four-dimensional periodic chi-neighborhood of rootQ.

This file proves that these two descriptions have exactly the
same bulk-q contact, including when the torus wraps around,
and that the augmented bulk-bulk contact agrees with the old U2
geometry. Consequently the q species is not a free new
incompatibility relation; the ONLY extra augmented edge possible
relative to the original graph is direct contact p-q, which
the original connected graph explicitly excludes.

Full planar-tree/root-forest enumeration and actual CMP122
history-to-polymer identification are still separate obligations.
-/

/-- The old U2 bulk-bulk contact survives q augmentation EXACTLY:
no extra link among ordinary bulk polymers is created. -/
theorem actual_augmented_bulk_children_iff_original
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (rootQ : Finset (PeriodicBlock N))
    (X Y : Γ) :
    (Sum.inl Y : Sum Γ Unit) ∈
        actualPeriodicPolymerChildren N chi
          (actualSecondRootAugmentedSupport N support rootQ)
          (Sum.inl X) ↔
      Y ∈ actualPeriodicPolymerChildren N chi support X := by
  classical
  change
    (Sum.inl Y : Sum Γ Unit) ∈
      (Finset.univ : Finset (Sum Γ Unit)).filter
        (fun W => ∃ Delta ∈ actualRootNeighbourhood
          (support X) (fourDimPeriodicNeighborhood N chi),
          Delta ∈ actualSecondRootAugmentedSupport N support rootQ W)
      ↔
    Y ∈ (Finset.univ : Finset Γ).filter
        (fun W => ∃ Delta ∈ actualRootNeighbourhood
          (support X) (fourDimPeriodicNeighborhood N chi),
          Delta ∈ support W)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    actualSecondRootAugmentedSupport]

/-- A physical q-root edge to the bulk polymer X is EXACTLY the
first-child contact of the augmented q-species with X.
No arbitrary graph adjacency or abstract external root relation
is introduced. -/
theorem actual_augmented_second_root_bulk_contact_iff
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (rootQ : Finset (PeriodicBlock N))
    (X : Γ) :
    (Sum.inr () : Sum Γ Unit) ∈
        actualPeriodicPolymerChildren N chi
          (actualSecondRootAugmentedSupport N support rootQ)
          (Sum.inl X) ↔
      X ∈ actualContactRoot rootQ
        (fourDimPeriodicNeighborhood N chi) support := by
  classical
  rw [actual_periodic_polymer_children_symm N chi
    (actualSecondRootAugmentedSupport N support rootQ)
    (Sum.inl X) (Sum.inr ())]
  change
    (Sum.inl X : Sum Γ Unit) ∈
      (Finset.univ : Finset (Sum Γ Unit)).filter
        (fun W => ∃ Delta ∈ actualRootNeighbourhood
          rootQ (fourDimPeriodicNeighborhood N chi),
          Delta ∈ actualSecondRootAugmentedSupport N support rootQ W)
      ↔
    X ∈ (Finset.univ : Finset Γ).filter
        (fun W => ∃ Delta ∈ actualRootNeighbourhood
          rootQ (fourDimPeriodicNeighborhood N chi),
          Delta ∈ support W)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    actualSecondRootAugmentedSupport]

/-- The augmented system's possible extra *direct* p--q edge is
exactly actual physical chi-contact of the two fixed Wilson
root supports, whereas the manuscript's extended Ursell graph
has no p--q bond. Keeping this edge in a positive comparison
overcounts (is safe) and never undercounts the target trees. -/
theorem actual_augmented_pq_contact_iff
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (rootP rootQ : Finset (PeriodicBlock N)) :
    (Sum.inr () : Sum Γ Unit) ∈
        actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi)
          (actualSecondRootAugmentedSupport N support rootQ) ↔
      ∃ Delta ∈ actualRootNeighbourhood rootP
        (fourDimPeriodicNeighborhood N chi),
          Delta ∈ rootQ := by
  classical
  change
    (Sum.inr () : Sum Γ Unit) ∈
      (Finset.univ : Finset (Sum Γ Unit)).filter
        (fun W => ∃ Delta ∈ actualRootNeighbourhood
          rootP (fourDimPeriodicNeighborhood N chi),
          Delta ∈ actualSecondRootAugmentedSupport N support rootQ W)
      ↔
    ∃ Delta ∈ actualRootNeighbourhood
      rootP (fourDimPeriodicNeighborhood N chi), Delta ∈ rootQ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    actualSecondRootAugmentedSupport]

end YMUIC.Original24
