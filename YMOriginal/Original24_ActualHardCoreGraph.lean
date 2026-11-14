import YMOriginal.Original24_PeriodicRootTreeLimit
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Actual hard-core incompatibility graph of real periodic SU2 polymer supports

This file removes an abstract incompatibility graph parameter from
the C29 Penrose/FP route. For every periodic N^4 physical block
model, a polymer is a genuine FINITE block support. Two polymers
are hard-core incompatible when they have overlapping chi-contact
neighborhoods (in either ordered direction), or are the same species.

The repeated-label case is important: two different labeled
vertices carrying the SAME polymer species are incompatible.
The physical labeled cluster graph is on Fin n, NOT on the
species Γ. No analytic tree-graph bound is assumed or derived here.
-/

/-- Real physical chi-contact of two finite periodic polymer supports.
The disjunction makes the contact symmetric without silently
assuming reversibility of a periodic neighbor dictionary. -/
def actualPeriodicHardCoreIncompatible
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (X Y : Γ) : Prop :=
  X = Y ∨
    X ∈ actualPeriodicPolymerChildren N chi support Y ∨
    Y ∈ actualPeriodicPolymerChildren N chi support X

theorem actual_periodic_hardcore_incompatible_refl
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (X : Γ) :
    actualPeriodicHardCoreIncompatible N chi support X X :=
  Or.inl rfl

theorem actual_periodic_hardcore_incompatible_symm
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (X Y : Γ) :
    actualPeriodicHardCoreIncompatible N chi support X Y ↔
      actualPeriodicHardCoreIncompatible N chi support Y X := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · intro h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- Actual finite periodic polymer incompatibility as a loopless graph
on distinct species; same-species exclusion is kept separately by
the reflexive relation above. -/
def actualPeriodicHardCoreSpeciesGraph
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N)) :
    SimpleGraph Γ :=
  SimpleGraph.fromRel (actualPeriodicHardCoreIncompatible N chi support)

theorem actual_periodic_hardcore_species_adj
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (X Y : Γ) :
    (actualPeriodicHardCoreSpeciesGraph N chi support).Adj X Y ↔
      X ≠ Y ∧ actualPeriodicHardCoreIncompatible N chi support X Y := by
  rw [actualPeriodicHardCoreSpeciesGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, (actual_periodic_hardcore_incompatible_symm
        N chi support Y X).mp h⟩
  · rintro ⟨hne, hc⟩
    exact ⟨hne, Or.inl hc⟩

/-- Actual labeled hard-core graph on distinct INSERTION VERTICES.
Even two labels carrying the SAME polymer X remain adjacent (because
the species-level incompatibility relation is reflexive).
Thus the factorial Mayer graph expansion correctly treats
repeated species. -/
def actualPeriodicLabeledHardCoreGraph
    {Γ : Type*} [Fintype Γ] (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j =>
    actualPeriodicHardCoreIncompatible N chi support (tuple i) (tuple j))

theorem actual_periodic_labeled_hardcore_adj
    {Γ : Type*} [Fintype Γ] (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) (i j : Fin n) :
    (actualPeriodicLabeledHardCoreGraph n N chi support tuple).Adj i j ↔
      i ≠ j ∧
        actualPeriodicHardCoreIncompatible N chi support
          (tuple i) (tuple j) := by
  rw [actualPeriodicLabeledHardCoreGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, (actual_periodic_hardcore_incompatible_symm
        N chi support (tuple j) (tuple i)).mp h⟩
  · rintro ⟨hne, hc⟩
    exact ⟨hne, Or.inl hc⟩

/-- Exact hard-core Mayer bond, not an abstract complex number:
-1 for incompatible species (including self-contact), zero otherwise. -/
def actualPeriodicMayerBond
    {Γ : Type*} [Fintype Γ] (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (X Y : Γ) : ℝ := by
  classical
  exact if actualPeriodicHardCoreIncompatible N chi support X Y then -1 else 0

theorem actual_periodic_mayer_bond_self
    {Γ : Type*} [Fintype Γ] (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N)) (X : Γ) :
    actualPeriodicMayerBond N chi support X X = -1 := by
  classical
  simp [actualPeriodicMayerBond,
    actual_periodic_hardcore_incompatible_refl]

theorem actual_periodic_mayer_bond_symm
    {Γ : Type*} [Fintype Γ] (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N)) (X Y : Γ) :
    actualPeriodicMayerBond N chi support X Y =
      actualPeriodicMayerBond N chi support Y X := by
  classical
  by_cases h : actualPeriodicHardCoreIncompatible N chi support X Y
  · have h' :=
      (actual_periodic_hardcore_incompatible_symm
        N chi support X Y).mp h
    simp [actualPeriodicMayerBond, h, h']
  · have h' : ¬ actualPeriodicHardCoreIncompatible N chi support Y X := by
      intro hy
      exact h ((actual_periodic_hardcore_incompatible_symm
        N chi support Y X).mp hy)
    simp [actualPeriodicMayerBond, h, h']

theorem actual_periodic_mayer_bond_norm_le_one
    {Γ : Type*} [Fintype Γ] (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N)) (X Y : Γ) :
    |actualPeriodicMayerBond N chi support X Y| ≤ 1 := by
  classical
  by_cases h :
      actualPeriodicHardCoreIncompatible N chi support X Y
  · simp [actualPeriodicMayerBond, h]
  · simp [actualPeriodicMayerBond, h]

/-- A literal bond is nonzero iff the actual physical periodic
hard-core incompatibility holds, including self-repeated species. -/
theorem actual_periodic_mayer_bond_ne_zero_iff
    {Γ : Type*} [Fintype Γ] (N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N)) (X Y : Γ) :
    actualPeriodicMayerBond N chi support X Y ≠ 0 ↔
      actualPeriodicHardCoreIncompatible N chi support X Y := by
  classical
  by_cases h :
      actualPeriodicHardCoreIncompatible N chi support X Y
  · simp [actualPeriodicMayerBond, h]
  · simp [actualPeriodicMayerBond, h]

/-- For distinct labeled histories, a nonzero Mayer bond is
EXACTLY one edge of the actual physical graph. -/
theorem actual_periodic_labeled_mayer_edge
    {Γ : Type*} [Fintype Γ] (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) (i j : Fin n)
    (hij : i ≠ j) :
    (actualPeriodicLabeledHardCoreGraph n N chi support tuple).Adj i j ↔
      actualPeriodicMayerBond N chi support (tuple i) (tuple j) ≠ 0 := by
  rw [actual_periodic_labeled_hardcore_adj,
    actual_periodic_mayer_bond_ne_zero_iff]
  simp [hij]

end YMUIC.Original24
