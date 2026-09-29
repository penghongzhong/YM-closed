import Mathlib

set_option autoImplicit false

/-!
# U2 root-distance: getVert/support sum bridge

Standalone bookkeeping bridge for the final assembly of v133
`lem:root-distance`.

For every walk p and weight f,
  sum_{k < length(p)+1} f(p.getVert k)
equals the sum of f over the ordered support list.
For a simple path the support list is duplicate-free, so this is bounded by
the total radius over the whole extended rooted-cluster vertex set.
-/

namespace YMUICV128.Section03.T005F

abbrev RootLabel := Fin 2
abbrev ExtendedVertex (n : ℕ) := Sum (Fin n) RootLabel

def vertexRadius {n : ℕ} (d : Fin n → ℕ) (R : ℕ) :
    ExtendedVertex n → ℕ
  | Sum.inl i => d i
  | Sum.inr _ => R

theorem getVert_range_sum_eq_support_sum
    {V : Type*}
    {G : SimpleGraph V}
    (f : V → ℕ)
    {u v : V}
    (p : G.Walk u v) :
    (Finset.range (p.length + 1)).sum
        (fun k => f (p.getVert k))
      = (p.support.map f).sum := by
  induction p with
  | nil =>
      simp
  | @cons u v w h p ih =>
      calc
        (Finset.range ((p.cons h).length + 1)).sum
            (fun k => f ((p.cons h).getVert k))
            =
          f u + (Finset.range (p.length + 1)).sum
            (fun k => f (p.getVert k)) := by
              rw [show (p.cons h).length + 1 = (p.length + 1) + 1 by simp]
              rw [Finset.sum_range_succ']
              simp [Nat.add_comm]
        _ = f u + (p.support.map f).sum := by
              rw [ih]
        _ = ((p.cons h).support.map f).sum := by
              simp

theorem total_vertexRadius
    {n : ℕ}
    (d : Fin n → ℕ)
    (R : ℕ) :
    (∑ v : ExtendedVertex n, vertexRadius d R v)
      = (∑ i : Fin n, d i) + 2 * R := by
  rw [Fintype.sum_sum_type]
  simp [vertexRadius, Fin.sum_univ_two, two_mul]

theorem simple_path_getVert_radius_sum_le_total
    {n : ℕ}
    {H : SimpleGraph (ExtendedVertex n)}
    {u v : ExtendedVertex n}
    (p : H.Walk u v)
    (hp : p.IsPath)
    (d : Fin n → ℕ)
    (R : ℕ) :
    (Finset.range (p.length + 1)).sum
        (fun k => vertexRadius d R (p.getVert k))
      ≤ (∑ i : Fin n, d i) + 2 * R := by
  classical
  rw [getVert_range_sum_eq_support_sum]
  calc
    (p.support.map (vertexRadius d R)).sum
        = ∑ x ∈ p.support.toFinset, vertexRadius d R x := by
            symm
            exact List.sum_toFinset _ hp.support_nodup
    _ ≤ ∑ x ∈ (Finset.univ : Finset (ExtendedVertex n)),
          vertexRadius d R x :=
      Finset.sum_le_sum_of_subset (by
        intro x hx
        simp)
    _ = ∑ x : ExtendedVertex n, vertexRadius d R x := by
      rfl
    _ = (∑ i : Fin n, d i) + 2 * R :=
      total_vertexRadius d R

#print axioms getVert_range_sum_eq_support_sum
#print axioms total_vertexRadius
#print axioms simple_path_getVert_radius_sum_le_total

end YMUICV128.Section03.T005F
