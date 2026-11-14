import YMOriginal.Original24_PeriodicFourDimContact
import YMOriginal.Original24_ActualLatticeLinks

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Fixed-complexity ACTUAL Wilson link-root support cost

A closed Wilson loop at base p uses only the finite vertex list
base :: w.vertices. For a family of <= M loops, each with <= L links,
the total physical root support has at most M*(L+1) blocks. This
bound is uniform in lattice spacing, UV cutoff, volume, and background.

Combine with the STRICTLY VERIFIED periodic N^4 neighbor counting
to obtain the real U2 first-root contact amplitude directly from
the U1 per-block activity norm, with the exact fixed-D root
complexity constant M*(L+1)*(2chi+1)^4, not an assumed Nroot.
-/

def actualClosedWilsonRootBlocks
    {Vertex : Type*} (base : Vertex)
    (w : ClosedLinkWalkAt Vertex base) : Finset Vertex := by
  classical
  exact insert base w.vertices.toFinset

theorem actual_closed_wilson_root_blocks_card
    {Vertex : Type*}
    (base : Vertex) (w : ClosedLinkWalkAt Vertex base) :
    (actualClosedWilsonRootBlocks base w).card ≤
      w.vertices.length + 1 := by
  classical
  unfold actualClosedWilsonRootBlocks
  calc
    (insert base w.vertices.toFinset).card ≤
      w.vertices.toFinset.card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ w.vertices.length + 1 :=
      Nat.add_le_add_right (List.toFinset_card_le _) _

/-- Root support for any finite fixed-complexity family of genuine
closed Wilson loops at the same base lattice vertex. -/
def actualFiniteWilsonRootFamilyBlocks
    {Vertex : Type*} (base : Vertex)
    (loops : Finset (ClosedLinkWalkAt Vertex base)) :
    Finset Vertex := by
  classical
  exact loops.biUnion (actualClosedWilsonRootBlocks base)

/-- The ROOT cost is exactly family size times (max-link-count+1).
This replaces an untracked physical-support assumption. -/
theorem actual_finite_wilson_root_family_card
    {Vertex : Type*}
    (base : Vertex)
    (loops : Finset (ClosedLinkWalkAt Vertex base))
    (L : ℕ)
    (hLen : ∀ w ∈ loops, w.vertices.length ≤ L) :
    (actualFiniteWilsonRootFamilyBlocks base loops).card ≤
      loops.card * (L + 1) := by
  classical
  unfold actualFiniteWilsonRootFamilyBlocks
  calc
    (loops.biUnion (actualClosedWilsonRootBlocks base)).card ≤
      ∑ w ∈ loops, (actualClosedWilsonRootBlocks base w).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ loops, (L + 1) := by
      apply Finset.sum_le_sum
      intro w hw
      exact (actual_closed_wilson_root_blocks_card base w).trans
        (Nat.add_le_add_right (hLen w hw) 1)
    _ = loops.card * (L + 1) := by
      simp [Nat.mul_comm]

/-- Real finite-complexity Wilson source root: U1 local block activity
and true periodic 4D coordination imply the root-contact total.
No marked-root total or graph-independent root-support bound is a premise.
-/
theorem actual_fixed_wilson_family_root_from_U1
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (base : PeriodicBlock N)
    (loops : Finset (ClosedLinkWalkAt (PeriodicBlock N) base))
    (L : ℕ)
    (hLen : ∀ w ∈ loops, w.vertices.length ≤ L)
    (support : Γ → Finset (PeriodicBlock N))
    (weight : Γ → ℝ) (aAct : ℝ)
    (hweight : ∀ X, 0 ≤ weight X)
    (haAct : 0 ≤ aAct)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta, weight X) ≤ aAct) :
    (∑ X ∈ actualContactRoot
      (actualFiniteWilsonRootFamilyBlocks base loops)
      (fourDimPeriodicNeighborhood N chi) support, weight X) ≤
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        ((loops.card * (L + 1) : ℕ) : ℝ) * aAct := by
  let root := actualFiniteWilsonRootFamilyBlocks base loops
  have hRootCard := actual_finite_wilson_root_family_card
    base loops L hLen
  have hCard :
      (root.card : ℝ) ≤ ((loops.card * (L + 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hRootCard
  have hStart := periodic_four_dim_root_contact_from_U1_norm
    N chi root support weight aAct hweight haAct hLocalNorm
  calc
    (∑ X ∈ actualContactRoot root
      (fourDimPeriodicNeighborhood N chi) support, weight X) ≤
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ) * aAct := hStart
    _ = ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct) *
        (root.card : ℝ) := by ring
    _ ≤ ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct) *
        ((loops.card * (L + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hCard
          (mul_nonneg (Nat.cast_nonneg _) haAct)
    _ = (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        ((loops.card * (L + 1) : ℕ) : ℝ) * aAct := by ring

end YMUIC.Original24
