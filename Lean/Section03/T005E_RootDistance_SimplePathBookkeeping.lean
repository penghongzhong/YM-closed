import Mathlib

set_option autoImplicit false

/-!
# U2 root-distance: simple-path bookkeeping

Standalone finite combinatorics for the final assembly of v133
`lem:root-distance`.

The extended rooted-cluster vertex type has n bulk labels and two roots.
For any simple path in that graph:
* its edge length is at most n+1;
* if every bulk length d(i) is at least 1, then n ≤ D := ∑ d(i);
* hence the path length is at most D+1;
* the total radius of all vertices visited by the simple path is bounded by
  the radius sum over the whole extended vertex set, namely D+2R.

No contact geometry is used in this file.
-/

namespace YMUICV128.Section03.T005E

abbrev RootLabel := Fin 2
abbrev ExtendedVertex (n : ℕ) := Sum (Fin n) RootLabel

def vertexRadius {n : ℕ} (d : Fin n → ℕ) (R : ℕ) :
    ExtendedVertex n → ℕ
  | Sum.inl i => d i
  | Sum.inr _ => R

theorem extendedVertex_card (n : ℕ) :
    Fintype.card (ExtendedVertex n) = n + 2 := by
  simp [ExtendedVertex, RootLabel]

theorem simple_root_path_length_le
    {n : ℕ}
    {H : SimpleGraph (ExtendedVertex n)}
    {u v : ExtendedVertex n}
    (p : H.Walk u v)
    (hp : p.IsPath) :
    p.length ≤ n + 1 := by
  have hlt : p.length < Fintype.card (ExtendedVertex n) :=
    hp.length_lt
  rw [extendedVertex_card] at hlt
  omega

theorem bulk_count_le_total_length
    {n : ℕ}
    (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, 1 ≤ d i) :
    n ≤ ∑ i : Fin n, d i := by
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, d i := by
      exact Finset.sum_le_sum fun i _ => hd i

theorem simple_root_path_length_le_total
    {n : ℕ}
    {H : SimpleGraph (ExtendedVertex n)}
    {u v : ExtendedVertex n}
    (p : H.Walk u v)
    (hp : p.IsPath)
    (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, 1 ≤ d i) :
    p.length ≤ (∑ i : Fin n, d i) + 1 := by
  have hpath := simple_root_path_length_le p hp
  have hbulk := bulk_count_le_total_length d hd
  omega

theorem total_vertexRadius
    {n : ℕ}
    (d : Fin n → ℕ)
    (R : ℕ) :
    (∑ v : ExtendedVertex n, vertexRadius d R v)
      = (∑ i : Fin n, d i) + 2 * R := by
  rw [Fintype.sum_sum_type]
  simp [vertexRadius, Fin.sum_univ_two, two_mul]

theorem simple_path_support_radius_sum_le_total
    {n : ℕ}
    {H : SimpleGraph (ExtendedVertex n)}
    {u v : ExtendedVertex n}
    (p : H.Walk u v)
    (hp : p.IsPath)
    (d : Fin n → ℕ)
    (R : ℕ) :
    (∑ x ∈ p.support.toFinset, vertexRadius d R x)
      ≤ (∑ i : Fin n, d i) + 2 * R := by
  classical
  have hsubset :
      p.support.toFinset ⊆
        (Finset.univ : Finset (ExtendedVertex n)) := by
    intro x hx
    simp
  calc
    (∑ x ∈ p.support.toFinset, vertexRadius d R x)
        ≤ ∑ x ∈ (Finset.univ : Finset (ExtendedVertex n)),
            vertexRadius d R x :=
      Finset.sum_le_sum_of_subset hsubset
    _ = ∑ x : ExtendedVertex n, vertexRadius d R x := by
      rfl
    _ = (∑ i : Fin n, d i) + 2 * R :=
      total_vertexRadius d R

#print axioms extendedVertex_card
#print axioms simple_root_path_length_le
#print axioms bulk_count_le_total_length
#print axioms simple_root_path_length_le_total
#print axioms total_vertexRadius
#print axioms simple_path_support_radius_sum_le_total

end YMUICV128.Section03.T005E
