import Mathlib

/-!
# Registered external interfaces

This file is a provenance/type registry only.  It contains no custom axioms.
Every external theorem used later must be passed explicitly as a hypothesis or
encoded by a structure field in the theorem file that uses it.

Current U1 sources recorded from the synchronized v133 manuscript:
* Balaban CMP109: localized small-field representation / analytic domain /
  exponential localization / inductive preservation.
* Balaban CMP116: connected-cluster activity and exponential estimates.
* Balaban CMP119: old-R power bound and Ward–Taylor subtraction.
* Balaban CMP122: complete-density induction and new-boundary R term.

The exact page/equation dictionary remains in paper/CURRENT.
-/

namespace YMUICV128.Interfaces

structure SourceRecord where
  shortName : String
  locator : String
  role : String

def cmp109 : SourceRecord :=
  ⟨"CMP109", "(1.7),(1.9),(1.18)-(1.22), Theorem 3", "small-field localized/analytic induction"⟩

def cmp116 : SourceRecord :=
  ⟨"CMP116", "(2.11)-(2.13),(2.38)-(2.41), Lemma 3", "connected-cluster exponential localization"⟩

def cmp119 : SourceRecord :=
  ⟨"CMP119", "(2.30)-(2.33), Theorems 1-2, (2.43)-(2.44), (3.48)-(3.67)", "old-R and Ward-Taylor subtraction"⟩

def cmp122 : SourceRecord :=
  ⟨"CMP122", "Theorem 1, (1.90)-(1.104)", "complete-density/new-boundary induction"⟩

def fernandezProcacciPenrose : SourceRecord :=
  ⟨"Fernandez-Procacci CMP274 (2007)",
    "Proposition 5, equation (4.3), spanning-tree majorant (4.5)",
    "hard-core Penrose pointwise connected-Ursell tree-graph inequality"⟩

def fernandezProcacciRootedTrees : SourceRecord :=
  ⟨"Fernandez-Procacci CMP274 (2007)",
    "Section 4.1, Propositions 7-8, equations (4.12)-(4.19)",
    "finite-height planar-rooted-tree iteration and conversion to factorial-normalized labeled rooted trees"⟩

end YMUICV128.Interfaces
