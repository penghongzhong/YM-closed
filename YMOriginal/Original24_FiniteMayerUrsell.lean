import YMOriginal.Original24_ActualHardCoreGraph
import YMOriginal.Original01_U1PublishedBridge
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUICV128.Section02

/-!
# Explicit finite hard-core Mayer--Ursell connected graph source

For each physical periodic polymer species set Γ, with real 4D
block supports and the EXACT hard-core -1/0 Mayer bond, define
the genuine connected Mayer coefficient by the finite sum
  Phi^T(gamma_1,...,gamma_n)
     = Sum_{G connected, E(G) subset Incompat(tuple)} (-1)^|E(G)|.
This sums LABELED spanning connected subgraphs with all repetitions
retained, no chosen abstract Phi_n.

The unmarked coefficient uses the exact 1/n! symmetry factor, and
the original Bałaban U1Data.oldR/newR at the SAME RG scale and
background are inserted literally, not through an arbitrary z.

The Penrose TREE inequality and FP rooted enumeration for these
specific coefficients remain separate mathematical work. The
finite coefficient itself and its support/zero property are
proved without any external tree bound or extra axiom.
-/

/-- Literal hard-core Mayer--Ursell coefficient on n+1 labeled
history vertices: sum of (-1)^number-of-edges over ALL connected
simple subgraphs compatible with the actual physical adjacency. -/
def actualPeriodicConnectedMayerCoefficient
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ) : ℝ := by
  classical
  exact ∑ H : SimpleGraph (Fin (n + 1)),
    if H ≤ actualPeriodicLabeledHardCoreGraph
        (n + 1) N chi support tuple ∧ H.Connected
    then (-1 : ℝ) ^ H.edgeFinset.card
    else 0

/-- A disconnected ACTUAL hard-core incompatibility graph has zero
connected Mayer coefficient: every graph in the defining sum is
forced to be disconnected. No abstract connected coefficient input. -/
theorem actual_periodic_connected_mayer_zero_of_disconnected
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ)
    (hDisc : ¬ (actualPeriodicLabeledHardCoreGraph
        (n + 1) N chi support tuple).Connected) :
    actualPeriodicConnectedMayerCoefficient n N chi support tuple = 0 := by
  classical
  unfold actualPeriodicConnectedMayerCoefficient
  apply Finset.sum_eq_zero
  intro H hH
  have hno : ¬
      (H ≤ actualPeriodicLabeledHardCoreGraph
          (n + 1) N chi support tuple ∧ H.Connected) := by
    rintro ⟨hHG, hConnected⟩
    exact hDisc (hConnected.mono hHG)
  simp [hno]

/-- Unconditional finite-size bound, with a REAL and exact graph-count
rather than a postulated Mayer-coefficient norm. The sharp Penrose
spanning-TREE bound is a distinct remaining input. -/
theorem actual_periodic_connected_mayer_abs_le_graph_count
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ) :
    |actualPeriodicConnectedMayerCoefficient n N chi support tuple| ≤
      (Fintype.card (SimpleGraph (Fin (n + 1))) : ℝ) := by
  classical
  let G : SimpleGraph (Fin (n + 1)) :=
    actualPeriodicLabeledHardCoreGraph (n + 1) N chi support tuple
  let term : SimpleGraph (Fin (n + 1)) → ℝ := fun H =>
    if H ≤ G ∧ H.Connected then (-1 : ℝ) ^ H.edgeFinset.card else 0
  have hterm (H : SimpleGraph (Fin (n + 1))) :
      ‖term H‖ ≤ 1 := by
    dsimp [term]
    split_ifs <;> simp
  have hid :
      actualPeriodicConnectedMayerCoefficient n N chi support tuple =
      ∑ H : SimpleGraph (Fin (n + 1)), term H := by
    simp [actualPeriodicConnectedMayerCoefficient, G, term]
  calc
    |actualPeriodicConnectedMayerCoefficient n N chi support tuple| =
      ‖∑ H : SimpleGraph (Fin (n + 1)), term H‖ := by
        rw [hid, Real.norm_eq_abs]
    _ ≤ ∑ H : SimpleGraph (Fin (n + 1)), ‖term H‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _H : SimpleGraph (Fin (n + 1)), (1 : ℝ) :=
      Finset.sum_le_sum (fun H _ => hterm H)
    _ = (Fintype.card (SimpleGraph (Fin (n + 1))) : ℝ) := by
      simp

/-- Genuine unmarked hard-core cluster coefficient, for n+1 labeled
histories, with the canonical 1/(n+1)! symmetry factor and exact
product of physical polymer activity coefficients. -/
def actualPeriodicUnmarkedMayerTerm
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) : ℂ := by
  classical
  exact (Nat.factorial (n + 1) : ℂ)⁻¹ *
    ∑ tuple : Fin (n + 1) → Γ,
      (actualPeriodicConnectedMayerCoefficient n N chi
        support tuple : ℂ) *
      ∏ i : Fin (n + 1), z (tuple i)

/-- Exactly the SAME Bałaban published U1 old-R histories are
the coefficients of the explicitly defined connected graph sum. -/
def actualBalabanOldRConnectedMayerTerm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω)
    (j n N chi : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N)) : ℂ :=
  actualPeriodicUnmarkedMayerTerm n N chi support (fun X => D.oldR j X omega)

/-- The companion new-R expansion uses precisely the SAME hard-core
physical support/incompatibility graph, not a substitute tree or
independent model. -/
def actualBalabanNewRConnectedMayerTerm
    {Γ Ω : Type*} [Fintype Γ]
    (D : U1Data Γ Ω)
    (j n N chi : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N)) : ℂ :=
  actualPeriodicUnmarkedMayerTerm n N chi support (fun X => D.newR j X omega)

end YMUIC.Original24
