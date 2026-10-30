import YMOriginal.Original24_ActualRootContactCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24

/-!
# Genuine 4D PERIODIC block-neighborhood cardinality for root attachments

For an actual periodic N^4 torus, blocks are x : Fin 4 -> ZMod N.
A physical root with contact radius chi uses all offsets
  δ_i in {-chi,...,+chi} (mod N).
The 4D neighborhood is an explicit FINITE IMAGE of these offsets, so
  |Neighbour_chi(x)| <= (2*chi+1)^4
uniformly in N, even if the torus wraps around or neighborhoods overlap.

Couple this with the previously proved root-contact cover and per-block
U1 activity norm. The resulting U2 one-root contact bound does NOT
presuppose the desired marked-R source bound or a separate Nchi smallness
hypothesis. The U1 local norm itself remains a published/model input.

This proves actual periodic placement combinatorics, NOT the
Fernandez--Procacci full connected two-root tree enumeration.
-/

/-- True periodic 4D lattice site with N periods. -/
abbrev PeriodicBlock (N : ℕ) := Fin 4 → ZMod N

/-- Each offset vector has exactly (2*chi+1)^4 possible labels.
The modular shifts automatically identify duplicate cells when N is
small or χ is larger than the period. -/
def fourDimPeriodicShift
    (N chi : ℕ) (x : PeriodicBlock N)
    (offset : Fin 4 → Fin (2 * chi + 1)) : PeriodicBlock N :=
  fun i => x i + (offset i).val - (chi : ZMod N)

/-- Actual closed/periodic 4D chi-contact neighborhood. -/
def fourDimPeriodicNeighborhood
    (N chi : ℕ) (x : PeriodicBlock N) :
    Finset (PeriodicBlock N) := by
  classical
  exact Finset.univ.image (fourDimPeriodicShift N chi x)

/-- Physical 4D coordination, exact uniform-in-N upper bound. -/
theorem four_dim_periodic_neighborhood_card
    (N chi : ℕ) (x : PeriodicBlock N) :
    (fourDimPeriodicNeighborhood N chi x).card ≤
      (2 * chi + 1) ^ 4 := by
  classical
  unfold fourDimPeriodicNeighborhood
  calc
    (Finset.univ.image (fourDimPeriodicShift N chi x)).card ≤
      (Finset.univ : Finset (Fin 4 → Fin (2 * chi + 1))).card :=
        Finset.card_image_le
    _ = (2 * chi + 1) ^ 4 := by
      simp [Fintype.card_fun, Fintype.card_fin]

/-- The REAL periodic N^4 4D root-contact bound, with both UV cutoff
N and physical volume absent from the root-count prefactor. -/
theorem periodic_four_dim_root_contact_from_U1_norm
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (weight : Γ → ℝ)
    (aAct : ℝ)
    (hweight : ∀ X, 0 ≤ weight X)
    (haAct : 0 ≤ aAct)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta, weight X) ≤ aAct) :
    (∑ X ∈ actualContactRoot root
      (fourDimPeriodicNeighborhood N chi) support, weight X) ≤
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (root.card : ℝ) * aAct := by
  exact actual_root_contact_sum_from_block_norm
    root (fourDimPeriodicNeighborhood N chi)
    support weight aAct ((2 * chi + 1) ^ 4)
    hweight haAct
    (fun Delta _ => four_dim_periodic_neighborhood_card N chi Delta)
    hLocalNorm

end YMUIC.Original24
