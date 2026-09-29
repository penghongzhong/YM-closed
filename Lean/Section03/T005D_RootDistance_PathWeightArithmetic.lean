import Mathlib

set_option autoImplicit false

/-!
# U2 root-distance: linear path-weight arithmetic

For a path with N edges and vertex radii ρ(0),...,ρ(N), summing
  ρ(k) + χ + ρ(k+1)
does not produce a quadratic loss:
  Σ_{k<N} (ρ(k)+χ+ρ(k+1))
    ≤ 2 Σ_{k<N+1} ρ(k) + χ N.

If N ≤ D+1, then the edge-count term is absorbed linearly:
  2D + χN ≤ (χ+2)D + χ.
-/

namespace YMUICV128.Section03.T005D

theorem prefix_radius_sum_le_full
    (ρ : ℕ → ℕ) (N : ℕ) :
    (Finset.range N).sum ρ
      ≤ (Finset.range (N + 1)).sum ρ := by
  calc
    (Finset.range N).sum ρ
        ≤ (Finset.range N).sum ρ + ρ N :=
          Nat.le_add_right _ _
    _ = (Finset.range (N + 1)).sum ρ := by
          rw [Finset.sum_range_succ]

theorem shifted_radius_sum_le_full
    (ρ : ℕ → ℕ) (N : ℕ) :
    (Finset.range N).sum (fun k => ρ (k + 1))
      ≤ (Finset.range (N + 1)).sum ρ := by
  rw [Finset.sum_range_succ']
  omega

theorem edge_radius_cost_sum_le
    (ρ : ℕ → ℕ) (χ N : ℕ) :
    (Finset.range N).sum
        (fun k => ρ k + χ + ρ (k + 1))
      ≤
    2 * (Finset.range (N + 1)).sum ρ + χ * N := by
  have h₁ := prefix_radius_sum_le_full ρ N
  have h₂ := shifted_radius_sum_le_full ρ N
  have hsplit :
      (Finset.range N).sum
          (fun k => ρ k + χ + ρ (k + 1))
        =
      (Finset.range N).sum ρ
        + χ * N
        + (Finset.range N).sum (fun k => ρ (k + 1)) := by
    simp [Finset.sum_add_distrib, Nat.mul_comm, add_assoc]
  rw [hsplit]
  omega

theorem absorb_edge_count
    {D χ N : ℕ}
    (hND : N ≤ D + 1) :
    2 * D + χ * N
      ≤ (χ + 2) * D + χ := by
  have hmul : χ * N ≤ χ * (D + 1) :=
    Nat.mul_le_mul_left χ hND
  calc
    2 * D + χ * N
        ≤ 2 * D + χ * (D + 1) :=
          Nat.add_le_add_left hmul (2 * D)
    _ = (χ + 2) * D + χ := by ring

#print axioms prefix_radius_sum_le_full
#print axioms shifted_radius_sum_le_full
#print axioms edge_radius_cost_sum_le
#print axioms absorb_edge_count

end YMUICV128.Section03.T005D
