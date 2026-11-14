import YMOriginal.Original24_FiniteMayerUrsell
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Exact published Penrose hard-core tree-graph identity use boundary

R. Fernández -- A. Procacci, Commun. Math. Phys. 274 (2007), 123-140,
Sec 4.1, Proposition 5, equations (4.3)--(4.6).
For a finite HARD-CORE incompatibility graph G on n+1 labeled
vertices the signed connected graph sum is bounded in absolute
value by the number of its SPANNING TREES.

Crucial distinction from the earlier modules:
- the physical connected coefficient is now DEFINED by the actual
  Fin (n+1) labeled graph and finite Mayer sum;
- the number of allowed spanning trees is an actual Finset of
  SimpleGraph objects with IsTree and T <= G;
- a single externally published UNIVERSAL combinatorial theorem
  is supplied as an explicit structure field for ALL finite G.
It is not a new axiom or a newly claimed Lean proof of Penrose.
-/

/-- The literal finite connected graph alternating sum in the
published Penrose identity. -/
def actualHardCoreConnectedGraphSum
    (n : ℕ) (G : SimpleGraph (Fin (n + 1))) : ℝ := by
  classical
  exact ∑ H : SimpleGraph (Fin (n + 1)),
    if H ≤ G ∧ H.Connected then
      (-1 : ℝ) ^ H.edgeFinset.card
    else 0

/-- An actual finite set of all SPANNING TREE subgraphs of
the finite incompatibility graph G, not an abstract count. -/
def actualHardCoreSpanningTrees
    (n : ℕ) (G : SimpleGraph (Fin (n + 1))) :
    Finset (SimpleGraph (Fin (n + 1))) := by
  classical
  exact Finset.univ.filter (fun T => T ≤ G ∧ T.IsTree)

/-- Published graph-combinatorial theorem as an explicit
external mathematical interface; universally quantified over
every finite hard-core simple graph. No physical Yang--Mills RG
estimate is part of this published result. -/
structure PublishedPenroseHardCoreTreeBound : Prop where
  tree_graph :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
      |actualHardCoreConnectedGraphSum n G| ≤
        (actualHardCoreSpanningTrees n G).card

/-- The actual hard-core Mayer coefficient of the TRUE 4D periodic
support graph is exactly the signed connected graph sum to which
the universal Penrose theorem applies. -/
theorem actual_periodic_mayer_eq_hardcore_graph_sum
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ) :
    actualPeriodicConnectedMayerCoefficient n N chi support tuple =
      actualHardCoreConnectedGraphSum n
        (actualPeriodicLabeledHardCoreGraph
          (n + 1) N chi support tuple) := by
  rfl

/-- A SINGLE correctly typed published Penrose input now gives the
precise spanning-TREE upper bound on the actual C29 finite history
Mayer coefficient, without postulating a coefficient-specific
hPenroseDistance or treating Phi_n as an arbitrary function.

The separate native graph-distance and FP infinite rooted
count remain physical/source-combinatorial obligations. -/
theorem actual_periodic_mayer_penrose_tree_bound
    (Published : PublishedPenroseHardCoreTreeBound)
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin (n + 1) → Γ) :
    |actualPeriodicConnectedMayerCoefficient n N chi support tuple| ≤
      (actualHardCoreSpanningTrees n
        (actualPeriodicLabeledHardCoreGraph
          (n + 1) N chi support tuple)).card := by
  rw [actual_periodic_mayer_eq_hardcore_graph_sum]
  exact Published.tree_graph n _

end YMUIC.Original24
