import YMOriginal.Original24_FiniteMayerUrsell
import YMOriginal.Original24_TwoExternalWilsonRoots

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24
open YMUICV128.Section02

/-!
# Literal finite hard-core two-root connected Mayer history coefficients

No arbitrary Phi_n remains: each coefficient is an exact finite
1/(n+1)! sum over tuples of REAL physical periodic polymer histories,
carrying the exact hard-core connected-graph Ursell coefficient
and the actual source-sector activity z(γ).

A tuple contributes ONLY when its connected bulk incompatibility
graph physically touches both Wilson root block supports.  For a
given actual Bałaban U1Data, separate oldR and newR series use the
SAME supports, graph, root conditions, RG level and background.

Crucial scope: a rooted connection-filtered hard-core Mayer series
is an explicit mathematical model, NOT yet a proof that the CMP119/122
large-field connected cumulant equals it. That identification and
its complete Penrose/FP infinite-sum bound remain open.
-/

/-- True physical two-root attachment for one finite labeled bulk
polymer tuple, with literal contact to BOTH external root supports. -/
def actualTwoRootPhysicalContact
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ) : Prop :=
  (∃ i : Fin (n + 1),
    tuple i ∈ actualContactRoot rootP
      (fourDimPeriodicNeighborhood N chi) support) ∧
  (∃ j : Fin (n + 1),
    tuple j ∈ actualContactRoot rootQ
      (fourDimPeriodicNeighborhood N chi) support)

/-- Actual two-root periodic contact is symmetric in p,q. -/
theorem actual_two_root_physical_contact_comm
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ) :
    actualTwoRootPhysicalContact n N chi rootP rootQ support tuple ↔
      actualTwoRootPhysicalContact n N chi rootQ rootP support tuple :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The genuinely LABELED n+1-history hard-core two-root cumulant
coefficient, with EXACT factorial 1/(n+1)! and with every
connected graph summed by the finite Mayer formula.
The root-contact filter is exact and the two physical Wilson roots
are external, not bulk polymer vertices. -/
def actualTwoRootHardCoreMayerTerm
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) : ℂ := by
  classical
  exact (Nat.factorial (n + 1) : ℂ)⁻¹ *
    ∑ tuple : Fin (n + 1) → Γ,
      if actualTwoRootPhysicalContact n N chi rootP rootQ support tuple then
        (actualPeriodicConnectedMayerCoefficient n N chi support tuple : ℂ) *
          (∏ i : Fin (n + 1), z (tuple i))
      else 0

/-- No single bulk history can touch p: every genuine double-root
connected coefficient vanishes. This zero is a FINITE GRAPH
consequence, not a postulated cluster-decay estimate. -/
theorem actual_two_root_mayer_zero_of_empty_first_contact
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ)
    (hEmpty : actualContactRoot rootP
        (fourDimPeriodicNeighborhood N chi) support = ∅) :
    actualTwoRootHardCoreMayerTerm n N chi rootP rootQ support z = 0 := by
  classical
  have hNoTuple (tuple : Fin (n + 1) → Γ) :
      ¬actualTwoRootPhysicalContact n N chi rootP rootQ support tuple := by
    intro h
    obtain ⟨⟨i,hi⟩, _⟩ := h
    rw [hEmpty] at hi
    simpa using hi
  unfold actualTwoRootHardCoreMayerTerm
  simp [hNoTuple]

/-- Finite rooted Mayer coefficients are unchanged when exchanging
the two source root SUPPORTS. The actual full source insertion
may be switched separately via the mixed source identity. -/
theorem actual_two_root_mayer_swap
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    actualTwoRootHardCoreMayerTerm n N chi rootP rootQ support z =
      actualTwoRootHardCoreMayerTerm n N chi rootQ rootP support z := by
  classical
  unfold actualTwoRootHardCoreMayerTerm
  congr 1
  apply Finset.sum_congr rfl
  intro tuple ht
  rw [actual_two_root_physical_contact_comm n N chi rootP rootQ
    support tuple]

/-- Same-history actual published Bałaban U1 old-R rooted series.
No arbitrary complex Phi_n or source-deformed CMP R-sector. -/
def actualBalabanOldRTwoRootHardCoreTerm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω) (j n N chi : ℕ) (omega : Ω)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) : ℂ :=
  actualTwoRootHardCoreMayerTerm n N chi rootP rootQ support
    (fun X => D.oldR j X omega)

/-- The actual new-R coefficients share the very same hard-core
connected-graph and two-root contact geometry as old-R. -/
def actualBalabanNewRTwoRootHardCoreTerm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω) (j n N chi : ℕ) (omega : Ω)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) : ℂ :=
  actualTwoRootHardCoreMayerTerm n N chi rootP rootQ support
    (fun X => D.newR j X omega)

end YMUIC.Original24
