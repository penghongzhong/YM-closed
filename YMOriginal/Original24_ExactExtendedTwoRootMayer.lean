import YMOriginal.Original24_FiniteMayerUrsell
import YMOriginal.Original24_PeriodicHardCoreEquivalence
import YMOriginal.Original24_ActualLatticeLinks
import YMOriginal.Original24_TwoExternalWilsonRoots

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24
open YMUICV128.Section02
open YMUICV128.Section03
open YMUIC.Wilson

/-!
# EXACT C29 manuscript two-root extended labeled hard-core Mayer graph

The original paper's rooted-cluster definition has vertex set
  V = Fin n ⊕ {r_p,r_q},
not merely its n bulk histories. This follows the original literally:
- n labeled bulk-polymer vertices with repeated species allowed;
- two DISTINCT external Wilson root vertices r_p and r_q;
- bulk-bulk edges exactly physical chi-incompatibility;
- root-bulk edges exactly physical chi-contact of root support;
- NO root-root edge;
- connected Ursell sum on the ENTIRE n+2-vertex graph;
- the exact symmetry factor 1/n!, not 1/(n+1)!;
- original Bałaban U1 old/new R activity products at the SAME level.

This corrects the earlier bulk-connected-only candidate:
Original24_TwoRootMayerSeries is NOT the manuscript two-root graph
and must not be used as a complete Original24 model.
The full infinite Penrose/FP estimate and CMP119/122 identification
remain independent obligations.
-/

/-- Exact physical adjacency on the paper's extended vertex set
Fin n ⊕ Fin 2, where the two Fin 2 vertices are r_p and r_q. -/
def actualExactTwoRootRelation
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    Sum (Fin n) (Fin 2) → Sum (Fin n) (Fin 2) → Prop
  | Sum.inl i, Sum.inl j =>
      actualPeriodicHardCoreIncompatible N chi support
        (tuple i) (tuple j)
  | Sum.inl i, Sum.inr k =>
      if k = 0 then
        tuple i ∈ actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi) support
      else
        tuple i ∈ actualContactRoot rootQ
          (fourDimPeriodicNeighborhood N chi) support
  | Sum.inr k, Sum.inl i =>
      if k = 0 then
        tuple i ∈ actualContactRoot rootP
          (fourDimPeriodicNeighborhood N chi) support
      else
        tuple i ∈ actualContactRoot rootQ
          (fourDimPeriodicNeighborhood N chi) support
  | Sum.inr _, Sum.inr _ => False

/-- The original n+2-vertex extended physical hard-core graph,
with no artificial root-root Mayer interaction. -/
def actualExactTwoRootGraph
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    SimpleGraph (Sum (Fin n) (Fin 2)) :=
  SimpleGraph.fromRel
    (actualExactTwoRootRelation n N chi rootP rootQ support tuple)

/-- The two external Wilson vertices NEVER have a direct Mayer
bond, exactly C29 manuscript equation (norootedge). -/
theorem actual_exact_two_root_no_root_bond
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    ¬(actualExactTwoRootGraph n N chi rootP rootQ support tuple).Adj
      (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)) := by
  simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
    SimpleGraph.fromRel_adj]

/-- The r_p-bulk edge is literally physical chi-contact with p. -/
theorem actual_exact_rootp_bulk_edge
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) (i : Fin n) :
    (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Adj
      (Sum.inr (0 : Fin 2)) (Sum.inl i) ↔
    tuple i ∈ actualContactRoot rootP
      (fourDimPeriodicNeighborhood N chi) support := by
  simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
    SimpleGraph.fromRel_adj]

/-- r_q-bulk edge exactly contacts the second external Wilson root. -/
theorem actual_exact_rootq_bulk_edge
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) (i : Fin n) :
    (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Adj
      (Sum.inr (1 : Fin 2)) (Sum.inl i) ↔
    tuple i ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support := by
  simp [actualExactTwoRootGraph, actualExactTwoRootRelation,
    SimpleGraph.fromRel_adj]

/-- The bulk-bulk bond is the exact physical incompatibility
(including repeated species with distinct labels), with no
unjustified assumption that every species has nonempty support. -/
theorem actual_exact_bulk_bulk_edge
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) (i j : Fin n) :
    (actualExactTwoRootGraph n N chi rootP rootQ support tuple).Adj
      (Sum.inl i) (Sum.inl j) ↔
    i ≠ j ∧
      actualPeriodicHardCoreIncompatible N chi support
        (tuple i) (tuple j) := by
  change (Sum.inl i ≠ Sum.inl j ∧
    (actualPeriodicHardCoreIncompatible N chi support
      (tuple i) (tuple j) ∨
     actualPeriodicHardCoreIncompatible N chi support
      (tuple j) (tuple i))) ↔ _
  constructor
  · rintro ⟨hne, h | h⟩
    · refine ⟨?_, h⟩
      intro hij
      exact hne (by rw [hij])
    · refine ⟨?_, ?_⟩
      · intro hij
        exact hne (by rw [hij])
      · exact (actual_periodic_hardcore_incompatible_symm
          N chi support (tuple j) (tuple i)).mp h
  · rintro ⟨hij, h⟩
    exact ⟨(fun hs => hij (Sum.inl.inj hs)), Or.inl h⟩

/-- Exact finite Mayer-Ursell coefficient on ALL extended vertices.
The connected graph sum has two extra root vertices and hard-core
Mayer bond -1 on every allowed graph edge. -/
def actualExactTwoRootUrsellCoefficient
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) : ℝ := by
  classical
  exact ∑ H : SimpleGraph (Sum (Fin n) (Fin 2)),
    if H ≤ actualExactTwoRootGraph n N chi rootP rootQ support tuple ∧
       H.Connected
    then (-1 : ℝ) ^ H.edgeFinset.card else 0

/-- Disconnected FULL extended graphs have zero Ursell coefficient,
with BOTH physical external Wilson roots included. -/
theorem actual_exact_two_root_ursell_zero_of_disconnected
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ)
    (hDisc :
      ¬(actualExactTwoRootGraph n N chi
        rootP rootQ support tuple).Connected) :
    actualExactTwoRootUrsellCoefficient
      n N chi rootP rootQ support tuple = 0 := by
  classical
  unfold actualExactTwoRootUrsellCoefficient
  apply Finset.sum_eq_zero
  intro H hH
  have hno : ¬
      (H ≤ actualExactTwoRootGraph n N chi rootP rootQ support tuple ∧
        H.Connected) := by
    rintro ⟨hle,hConn⟩
    exact hDisc (hConn.mono hle)
  simp [hno]

/-- EXACT manuscript nth finite two-root hard-core source
coefficient: 1/n! over bulk tuples, with Ursell on the
FULL extended n+2-vertex graph. -/
def actualExactTwoRootMayerTerm
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) : ℂ := by
  classical
  exact (Nat.factorial n : ℂ)⁻¹ *
    ∑ tuple : Fin n → Γ,
      if (actualExactTwoRootGraph
          n N chi rootP rootQ support tuple).Connected then
        (actualExactTwoRootUrsellCoefficient
          n N chi rootP rootQ support tuple : ℂ) *
          (∏ i : Fin n, z (tuple i))
      else 0

/-- The SAME published U1Data oldR and original background
are inserted into the exact extended Mayer graph. -/
def actualExactBalabanOldRTwoRootTerm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω) (j n N chi : ℕ) (omega : Ω)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) : ℂ :=
  actualExactTwoRootMayerTerm n N chi rootP rootQ support
    (fun X => D.oldR j X omega)

/-- NewR sector with precisely the same extended graph,
same physical root supports and the correct n! factor. -/
def actualExactBalabanNewRTwoRootTerm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω) (j n N chi : ℕ) (omega : Ω)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) : ℂ :=
  actualExactTwoRootMayerTerm n N chi rootP rootQ support
    (fun X => D.newR j X omega)

end YMUIC.Original24
