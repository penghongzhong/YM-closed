import YMOriginal.Original24_ExactExtendedTwoRootMayer
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Published Penrose identity specialized to EXACT C29 two-root graph

R. Fernández -- A. Procacci (2007), CMP 274, Prop. 5 and
equations (4.3)--(4.6): finite hard-core Mayer connected graph
sum is bounded in absolute value by its admissible spanning-tree
count. Here V = Fin n ⊕ Fin 2 has n bulk histories and EXACTLY two
distinct source roots, with no root--root bond.

The universal published combinatorial theorem is explicitly passed
as a TYPED EXTERNAL input. It is not a new Lean reproof, not a
custom axiom, and it does NOT assert that arbitrary Bałaban R
histories form this particular hard-core polymer model.
-/

/-- Published alternating connected graph sum on n+2 labeled vertices. -/
def exactExtendedConnectedGraphSum
    (n : ℕ) (G : SimpleGraph (Sum (Fin n) (Fin 2))) : ℝ := by
  classical
  exact ∑ H : SimpleGraph (Sum (Fin n) (Fin 2)),
    if H ≤ G ∧ H.Connected then (-1 : ℝ) ^ H.edgeFinset.card else 0

/-- ALL actual admissible spanning-tree subgraphs of the
n+2 vertex graph, with two separate physical root vertices. -/
def exactExtendedSpanningTrees
    (n : ℕ) (G : SimpleGraph (Sum (Fin n) (Fin 2))) :
    Finset (SimpleGraph (Sum (Fin n) (Fin 2))) := by
  classical
  exact Finset.univ.filter (fun T => T ≤ G ∧ T.IsTree)

/-- Correct published hard-core Penrose theorem as an explicit
external universally-quantified graph-combinatorial interface. -/
structure PublishedPenroseExtendedTwoRoot : Prop where
  bound :
    ∀ n (G : SimpleGraph (Sum (Fin n) (Fin 2))),
      |exactExtendedConnectedGraphSum n G| ≤
        ((exactExtendedSpanningTrees n G).card : ℝ)

/-- Concrete paper Ursell coefficient is DEFINITIONALLY the
finite connected graph sum on EXACT n+2 extended vertices. -/
theorem actual_exact_extended_ursell_eq_graph_sum
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    actualExactTwoRootUrsellCoefficient n N chi rootP rootQ support tuple =
      exactExtendedConnectedGraphSum n
        (actualExactTwoRootGraph n N chi rootP rootQ support tuple) := by
  rfl

/-- Applying published Penrose to the ACTUAL full extended graph,
not an arbitrary complex Phi_n and not a bulk-only graph. -/
theorem actual_exact_extended_penrose
    (P : PublishedPenroseExtendedTwoRoot)
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (tuple : Fin n → Γ) :
    |actualExactTwoRootUrsellCoefficient
       n N chi rootP rootQ support tuple| ≤
      ((exactExtendedSpanningTrees n
        (actualExactTwoRootGraph n N chi rootP rootQ support tuple)).card : ℝ) := by
  rw [actual_exact_extended_ursell_eq_graph_sum]
  exact P.bound n _

end YMUIC.Original24
