import Mathlib

set_option autoImplicit false

/-!
# v133 B01G: finite block graph / polymer / rooted-cluster encoding

Exact finite-volume object layer before lem:root-distance.
The twelve theorem nodes correspond to numbering, nonemptiness, in-support
reachability, finite enumeration, root-candidate cardinality, finite extended
vertex set, absence of a root-root bond, and root-to-root connectivity.
-/

namespace YMUICV128.Section03

abbrev Block (N : ℕ) := Fin N
abbrev BlockGraph (N : ℕ) := SimpleGraph (Block N)

def InSupportConnected {N : ℕ}
    (G : BlockGraph N) (X : Finset (Block N)) : Prop :=
  X.Nonempty ∧
    ∀ ⦃a b : Block N⦄, a ∈ X → b ∈ X →
      ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∈ X

abbrev Polymer {N : ℕ} (G : BlockGraph N) :=
  {X : Finset (Block N) // InSupportConnected G X}

theorem B01G01_block_numbering_card (N : ℕ) :
    Fintype.card (Block N) = N := by
  simp [Block]

theorem B01G02_polymer_nonempty
    {N : ℕ} {G : BlockGraph N} (X : Polymer G) :
    (X : Finset (Block N)).Nonempty :=
  X.property.1

theorem B01G03_polymer_subset_univ
    {N : ℕ} {G : BlockGraph N} (X : Polymer G) :
    (X : Finset (Block N)) ⊆ (Finset.univ : Finset (Block N)) := by
  intro v hv
  simp

theorem B01G04_in_support_reachability
    {N : ℕ} {G : BlockGraph N} (X : Polymer G)
    {a b : Block N}
    (ha : a ∈ (X : Finset (Block N)))
    (hb : b ∈ (X : Finset (Block N))) :
    ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∈ (X : Finset (Block N)) :=
  X.property.2 ha hb

theorem B01G05_polymer_type_finite
    {N : ℕ} (G : BlockGraph N) :
    Finite (Polymer G) := by
  infer_instance

theorem B01G06_labelled_tuple_type_finite
    {N n : ℕ} (G : BlockGraph N) :
    Finite (Fin n → Polymer G) := by
  infer_instance

def RootCandidate {N : ℕ} {G : BlockGraph N}
    (P : Polymer G → Prop) :=
  {X : Polymer G // P X}

theorem B01G07_root_candidate_type_finite
    {N : ℕ} {G : BlockGraph N} (P : Polymer G → Prop) :
    Finite (RootCandidate P) := by
  unfold RootCandidate
  infer_instance

theorem B01G08_root_candidate_card_le
    {N : ℕ} {G : BlockGraph N} (P : Polymer G → Prop) :
    Nat.card (RootCandidate P) ≤ Nat.card (Polymer G) := by
  change Nat.card {X : Polymer G // P X} ≤ Nat.card (Polymer G)
  exact Finite.card_subtype_le P

abbrev RootLabel := Fin 2

def rootP : RootLabel := 0
def rootQ : RootLabel := 1

abbrev ExtendedVertex (n : ℕ) := Sum (Fin n) RootLabel

theorem B01G09_extended_vertex_type_finite (n : ℕ) :
    Finite (ExtendedVertex n) := by
  infer_instance

def clusterRawRel {n : ℕ}
    (bulkContact : Fin n → Fin n → Prop)
    (pAttach qAttach : Fin n → Prop) :
    ExtendedVertex n → ExtendedVertex n → Prop
  | Sum.inl i, Sum.inl k => i ≠ k ∧ bulkContact i k
  | Sum.inr r, Sum.inl i =>
      if r = rootP then pAttach i else qAttach i
  | _, _ => False

def clusterGraph {n : ℕ}
    (bulkContact : Fin n → Fin n → Prop)
    (pAttach qAttach : Fin n → Prop) :
    SimpleGraph (ExtendedVertex n) :=
  SimpleGraph.fromRel (clusterRawRel bulkContact pAttach qAttach)

theorem B01G10_no_root_root_bond
    {n : ℕ}
    (bulkContact : Fin n → Fin n → Prop)
    (pAttach qAttach : Fin n → Prop) :
    ¬ (clusterGraph bulkContact pAttach qAttach).Adj
      (Sum.inr rootP) (Sum.inr rootQ) := by
  simp [clusterGraph, clusterRawRel]

theorem B01G11_connected_roots_reachable
    {n : ℕ}
    (bulkContact : Fin n → Fin n → Prop)
    (pAttach qAttach : Fin n → Prop)
    (hconn : (clusterGraph bulkContact pAttach qAttach).Connected) :
    (clusterGraph bulkContact pAttach qAttach).Reachable
      (Sum.inr rootP) (Sum.inr rootQ) :=
  hconn _ _

theorem B01G12_connected_roots_have_path
    {n : ℕ}
    (bulkContact : Fin n → Fin n → Prop)
    (pAttach qAttach : Fin n → Prop)
    (hconn : (clusterGraph bulkContact pAttach qAttach).Connected) :
    ∃ p :
        (clusterGraph bulkContact pAttach qAttach).Walk
          (Sum.inr rootP) (Sum.inr rootQ),
      p.IsPath :=
  hconn.exists_isPath _ _

#print axioms B01G01_block_numbering_card
#print axioms B01G02_polymer_nonempty
#print axioms B01G03_polymer_subset_univ
#print axioms B01G04_in_support_reachability
#print axioms B01G05_polymer_type_finite
#print axioms B01G06_labelled_tuple_type_finite
#print axioms B01G07_root_candidate_type_finite
#print axioms B01G08_root_candidate_card_le
#print axioms B01G09_extended_vertex_type_finite
#print axioms B01G10_no_root_root_bond
#print axioms B01G11_connected_roots_reachable
#print axioms B01G12_connected_roots_have_path

end YMUICV128.Section03
