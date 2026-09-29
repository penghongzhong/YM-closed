# F1 private manuscript synchronization record

Date: 2026-09-29.
Scope: private v133 CURRENT, subsection 8.5 and the entire RP1 section. No manuscript source or PDF is included in this repository.

## Verified editorial and algebraic checks

- Private PDF rebuilt: 69 pages.
- 677 distinct labels; duplicate labels 0; missing explicit references 0; explicit forward references 0.
- All 101 previous RP1 labels retained; 82 RP1 labels added for definitions, types, derivations and exact locators.
- RP1 has 17 proof environments. Their derivations are written entirely inside mathematical environments; no standalone prose proof paragraphs remain in that section.
- Corner values, conditional operators, integration domains, exterior variables, evaluation of holonomy, and the slab/slice embeddings are explicitly separated and defined.
- Original correlated Wilson conditional laws, coefficient cross terms, hypotheses and constants are retained. There is no substitution by a product law or a claimed physical-payment theorem.
- Parent exact-computation regression: 71 checks passed. F1 additional exact Pauli, ordered-word, derivative and threshold checks: 21 passed.
- Final XeLaTeX warnings, overfull and underfull counts: 0. Changed-page renders were inspected.

These are scoped editorial/algebraic checks, not a whole-manuscript semantic certification. The other inherited sections still require definition-by-definition and proof-gap review. Zero missing/forward labels is not a proof of zero semantic ambiguity.

## Lean and mathematical boundary

No Lean source, workflow, toolchain, or mathlib pin changed in this batch. No new theorem is promoted to Lean PASS. The certified RP1 helper source remains commit 8e14ed24b86d16de87192166b4c5976464898b71 with the evidence recorded in PROOF_REPAIR_RP1.md.

The continuous conditional-measure proofs are not end-to-end Lean-certified by the 25 existing helpers. I7-GLOBAL-ROOT-FRAME remains OPEN. Actual source membership, same-state/same-physical-window payment and remaining-state coverage remain explicit obligations.

Private CURRENT and its versioned F1 archive have been saved in the user's /YM Library. Frozen v128 is unchanged. This commit contains only this status record and intentionally does not request a duplicate CI execution for unchanged Lean code.
