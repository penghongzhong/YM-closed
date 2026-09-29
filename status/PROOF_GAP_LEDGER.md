# Proof-gap ledger

This ledger records only genuine mathematical gaps or overclaims exposed by formalization.

## Open mathematical gaps

### I7-GLOBAL-ROOT-FRAME — OPEN / GENUINE

Required internal statement: there exists a regulator-, volume-, UV-cutoff-, and exhaustion-independent `η* ∈ (0,1)` such that

`G0^(M) - G*^(M) ⪰ η* G0^(M)`

for every finite exhaustion level `M` (equivalently `G*^(M) ⪯ q* G0^(M)`, `q*=1-η*<1`).

The current private v133 synchronization manuscript explicitly records that v78 local relative-Gram positivity plus the v94 finite Farkas/root allocation only yields local/contact control with support-count loss and does not control cross terms of arbitrary interacting-measure linear combinations. Therefore the global quadratic-frame estimate is not presently derived from the registered premises.

Formal guardrail: `Lean/Audit/T900_LocalMargin_NotUniformFrame.lean` compiles with only standard mathlib axioms and exhibits positive semidefinite transfer/deficit forms with positive coordinate-axis relative margins but zero diagonal deficit. This proves only the logical non-implication from local margins to a global frame; it is not a Yang--Mills counterexample.

Consequence: `thm:gramtotransfer`, `thm:gap`, and unconditional U--I/U--I--C closure cannot be promoted to internal PASS until an independent interacting-measure quadratic-frame / dynamically equivalent estimate closes I7.

## Guardrails

- Do not convert an internal theorem into an axiom.
- Do not weaken a TeX theorem silently in Lean.
- Do not add the desired conclusion as a hypothesis.
- Do not call an abstract surrogate a proof of the paper theorem.
- External published inputs must have an exact source/variable dictionary before use.
- A failed compile is first classified as syntax / namespace / elaboration / API / statement mismatch; only the last category can create a proof-gap entry.


## Implementation-only incidents

- Commit `9bf5f3...`: T003/T004 had Lean implementation errors (missing `noncomputable`, syntax/elaboration issues). These are not mathematical gaps and are not promoted as PASS.


- T005A local import incident: `import Lean.Section03...` resolved into the Lean toolchain namespace and no local .olean existed. This is an implementation/module-layout issue, not a mathematical gap. T005A/T005B were converted to standalone certificates.


- T005D `omega` incident: the tactic failed to identify two definitionally equal Finset-sum forms in `prefix_radius_sum_le_full`; replaced by explicit monotonicity plus `Finset.sum_range_succ`. Classification: implementation-only, not a proof gap.


- root-distance definition audit: Lean required explicit finite-set graph distance, root-support diameter, and reachable contact witnesses. CURRENT TeX now defines these objects explicitly and replaces the existential constants by `c_geo=χ+2`, `c_rt=χ+4R_rt`. Classification: manuscript-definition clarification/strengthening, not a contradiction of the v128 claim.


## Closed formalization obligations

- root-distance final certification: T005A--T005G all compile under run #21; final outcome gate PASS; no `sorryAx`. CURRENT TeX carries the resulting explicit definitions/constants. No mathematical gap remains at this node.


- root-tree-majorant final certification: T006A--T006E are internal Lean PASS; T006F is the exact published Fernández–Procacci rooted-tree enumeration interface; T006G is the Lean assembly over that interface. Run #31 final gate and PDF job both PASS; no `sorryAx`. No genuine mathematical proof gap remains at this node.


- root-not-bulk-entropy final certification: T007A, T007C, T007D are internal Lean PASS; T007B uses only the exact Fernández–Procacci Penrose pointwise tree-graph inequality and proves the bounded-root factor internally. Full run #35 final gate PASS; raw logs contain no `sorryAx`. The analyticity sentence formerly appended to this proof is moved to the next analyticity lemma to preserve reverse dependency discipline.


- T008B source-derivative incident: the mathematical derivative formula was correct,
  but Lean initially failed to identify the named `clusterPhi` with the canonical
  lambda because of product-space/typeclass definitional normalization. The certificate
  now states the canonical lambda explicitly and proves the exact Fréchet derivative.
  Classification: implementation/API only; no mathematical gap.

- T008E derivative-majorant incident: implicit real/complex scalar arguments in
  `add_le_add` were not inferred. Replaced by an explicit
  `add_le_add_right` call with named scalar arguments.
  Classification: elaboration/API only; no mathematical gap.

## Source-analyticity closure

- `lem:U2-source-analyticity`: T008A--T008F all compile in raw Lean.
  Full synchronized run #58 final logical-order gate SUCCESS; CURRENT/v128 PDF sync SUCCESS.
  All printed axioms are restricted to `propext, Classical.choice, Quot.sound`;
  no `sorryAx`. The manuscript now states joint analyticity as joint complex
  Fréchet differentiability on the finite-dimensional source space `ℂ²`.
  No genuine mathematical proof gap remains at this node.


## Run #40 closure before the I7 boundary

At head `279a29531d46b166165c2d81eea6120a0f415a1a`, raw/full CI certifies T009A through T012F plus T900 with no `sorryAx`; final fast and full gates are SUCCESS. Hence U2 marked-shell, U3-A, corrected clock, and the complete B08 phase-lock chain are no longer open formalization obligations.
