import Mathlib

set_option autoImplicit false

/-!
# U2 root-distance: local polymer geometry

Standalone certificate for the first load-bearing internal step of v133
`lem:root-distance`.

The B01G polymer semantics are repeated minimally here so this file compiles
independently, without relying on a previously generated local .olean file.

For a polymer X and a,b ∈ X:
  dist_G(a,b) + 1 ≤ |X|.
Hence, from the manuscript's local length inequality |X| ≤ d_j(X),
  dist_G(a,b) ≤ d_j(X).

The full rooted-cluster/contact estimate is not claimed in this file.
-/

namespace YMUICV128.Section03.T005A

abbrev Block (N : ℕ) := Fin N
abbrev BlockGraph (N : ℕ) := SimpleGraph (Block N)

def InSupportConnected {N : ℕ}
    (G : BlockGraph N) (X : Finset (Block N)) : Prop :=
  X.Nonempty ∧
    ∀ ⦃a b : Block N⦄, a ∈ X → b ∈ X →
      ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∈ X

abbrev Polymer {N : ℕ} (G : BlockGraph N) :=
  {X : Finset (Block N) // InSupportConnected G X}

theorem polymer_internal_reachable
    {N : ℕ} {G : BlockGraph N} (X : Polymer G)
    {a b : Block N}
    (ha : a ∈ (X : Finset (Block N)))
    (hb : b ∈ (X : Finset (Block N))) :
    G.Reachable a b := by
  obtain ⟨w, _⟩ := X.property.2 ha hb
  exact w.reachable

theorem polymer_internal_dist_add_one_le_card
    {N : ℕ} {G : BlockGraph N} (X : Polymer G)
    {a b : Block N}
    (ha : a ∈ (X : Finset (Block N)))
    (hb : b ∈ (X : Finset (Block N))) :
    G.dist a b + 1 ≤ (X : Finset (Block N)).card := by
  classical
  obtain ⟨w, hwX⟩ := X.property.2 ha hb
  let p : G.Path a b := w.toPath
  have hp : (p : G.Walk a b).IsPath := p.property
  have hsupport :
      (p : G.Walk a b).support.toFinset ⊆
        (X : Finset (Block N)) := by
    intro v hv
    have hvp : v ∈ (p : G.Walk a b).support := by
      simpa using hv
    have hvw : v ∈ w.support := by
      exact w.support_toPath_subset_support hvp
    exact hwX v hvw
  have hcard :
      (p : G.Walk a b).support.toFinset.card ≤
        (X : Finset (Block N)).card :=
    Finset.card_le_card hsupport
  have hfin :
      (p : G.Walk a b).support.toFinset.card =
        (p : G.Walk a b).support.length :=
    List.toFinset_card_of_nodup hp.support_nodup
  have hlen :
      (p : G.Walk a b).length + 1 ≤
        (X : Finset (Block N)).card := by
    calc
      (p : G.Walk a b).length + 1
          = (p : G.Walk a b).support.length := by
              symm
              exact (p : G.Walk a b).length_support
      _ = (p : G.Walk a b).support.toFinset.card := hfin.symm
      _ ≤ (X : Finset (Block N)).card := hcard
  have hdist :
      G.dist a b ≤ (p : G.Walk a b).length :=
    SimpleGraph.dist_le (p : G.Walk a b)
  omega

theorem polymer_internal_dist_le_declared_length
    {N : ℕ} {G : BlockGraph N}
    (d : Polymer G → ℕ)
    (hcardLength :
      ∀ Y : Polymer G,
        (Y : Finset (Block N)).card ≤ d Y)
    (X : Polymer G)
    {a b : Block N}
    (ha : a ∈ (X : Finset (Block N)))
    (hb : b ∈ (X : Finset (Block N))) :
    G.dist a b ≤ d X := by
  have h₁ :=
    polymer_internal_dist_add_one_le_card X ha hb
  have h₂ := hcardLength X
  omega

#print axioms polymer_internal_reachable
#print axioms polymer_internal_dist_add_one_le_card
#print axioms polymer_internal_dist_le_declared_length

end YMUICV128.Section03.T005A
