# Lean status

Date: 2026-09-27

## Authority split

- Historical first fully-closed frozen master: v127.
- Frozen mathematical authority: v128.
- Reader/referee / Lean translation baseline: v133.
- Editable synchronized manuscript: `paper/CURRENT/YM_UIC_v133_LEAN_SYNC_CURRENT.tex`.

## Promotion classes

- **PASS**: exact internal statement compiled in raw Lean CI with no errors; no forbidden placeholders/custom axioms.
- **EXTERNAL-INTERFACE PASS**: exact use-boundary of a published/standard input type-checks; this does not claim a re-proof of the external theorem.
- **STAGED**: committed and awaiting a clean raw Lean run.
- **QUEUED**: not yet attempted in manuscript order.
- **GAP**: genuine mathematical missing argument/overclaim after implementation/API issues are ruled out.

## Actual raw-CI-certified nodes

1. §1 foundations — **PASS**.
2. §2 `thm:U1` Balaban input boundary — **EXTERNAL-INTERFACE PASS**.
3. §2 `δ_sf` positivity and geometric `tsum` core — **PASS**.
4. U2 Wilson root bound `0 ≤ W_p ≤ 4` — **PASS**.
5. U2 exact source multiplier bound `‖D_p(s)‖ ≤ exp(4r)-1` — **PASS**.
6. U2 B01G finite block/polymer/rooted-cluster object layer — **PASS (12/12)**.
7. U2 `lem:root-distance` — **PASS**.
   - T005A internal polymer geometry — PASS.
   - T005B mapped-walk metric budget — PASS.
   - T005C support-anchor one-edge budget — PASS.
   - T005D path-weight arithmetic — PASS.
   - T005E simple-path bookkeeping — PASS.
   - T005F getVert/support sum bridge — PASS.
   - T005G full assembly — PASS.
   - explicit constants:
     `c_geo = χ + 2`,
     `c_rt = χ + 4 R_rt`.

Run #21 (`522ae0c...`) finished with the full outcome gate **SUCCESS**.
Raw `#print axioms` for T005F/T005G contains no `sorryAx`; only standard
`propext, Classical.choice, Quot.sound`.

Forbidden-placeholder scan: **PASS**.
Synchronized v128/v133 PDF job: **PASS**.

## Current mathematical-gap status

A genuine load-bearing gap is now recorded at the first post-B08 Part-I node:

`I7-GLOBAL-ROOT-FRAME`

The current private v133 Lean-synchronization candidate states explicitly that the already certified local/rootwise deficit estimates and the v94 finite Farkas certificate do **not** imply the required regulator-uniform quadratic Gram inequality
`G0^(M) - G*^(M) ⪰ η* G0^(M)` for all finite exhaustion levels `M`.
Without an independent interacting-measure quadratic-frame / equivalent dynamical estimate, promoting this inequality to an internal theorem would assume an estimate equivalent in strength to the desired transfer contraction/mass gap.

`Lean/Audit/T900_LocalMargin_NotUniformFrame.lean` is a positive-contraction two-dimensional guardrail: it proves that nonnegative transfer/deficit forms can have uniform positive margins on the coordinate axes while the global relative deficit vanishes on the diagonal. This is **not** a counterexample to Yang--Mills; it certifies only that the local-to-global inference is invalid without extra structure.

This conflicts with the historical unconditional wording of frozen v128, so v128 is left untouched and the editable v133 synchronization layer records the conclusion conditionally until I7 is genuinely closed.

## Next logical order

`lem:root-tree-majorant`
→ `lem:root` (root not in bulk placement entropy)
→ `lem:U2-source-analyticity`
→ `thm:U2`
→ U3-A.


## Root-tree majorant decomposition

- `T006A_RootTreeMajorant_KPScalarCore.lean` — **PASS**.
  Scope: `δ>0`, the exact KP exponential identity, and the scalar
  `Nχ|X|a_* ≤ Aδ(X)` budget. The finite contact-counting inequality is
  intentionally not claimed yet.

- `T006B_RootTreeMajorant_ContactCounting.lean` — **PASS**.
  Scope: finite contact-cover/double-counting inequality
  `Σ_contact W ≤ |A| a ≤ Nχ a`.
- `T006C_RootTreeMajorant_FiniteHeightRecursion.lean` — **PASS**.
  Scope: exact finite-height recursion and induction
  `F_h(X) ≤ exp(Aδ(X))`.
- `T006D_RootTreeMajorant_FullChildSum.lean` — **PASS**.
  Scope: full finite `childsum` assembly, including damping,
  contact-cover cardinality, local activity norm, and
  `Nχ a_* ≤ δ/2`.
- `T006E_RootTreeMajorant_FirstRootSum.lean` — **PASS**.
  Scope: `F_h≤e^{Aδ}` plus root-neighbourhood counting gives
  `Σ_{X:p~χX} w(X)F_h(X) ≤ N_root a_j^{act}`.
- `T006F_RootTreeMajorant_FernandezProcacciInterface.lean` — **EXTERNAL-INTERFACE PASS**.
  Exact source: Fernández–Procacci, CMP 274 (2007), §4.1,
  Props. 7–8, equations (4.12)–(4.19). Only the tree-enumeration /
  factorial-normalization identification is external.
- `T006G_RootTreeMajorant_FullAssembly.lean` — **PASS over external combinatorial interface**.
  Final assembly: finite-height internal bound + Fernández–Procacci limit
  interface + two-root-domain inclusion.


## Newly closed theorem node

8. U2 `lem:root-tree-majorant` — **CLOSED / LEAN-CERTIFIED OVER EXTERNAL COMBINATORIAL INTERFACE**.
   - T006A KP scalar core — PASS.
   - T006B finite contact counting — PASS.
   - T006C finite-height recursion — PASS.
   - T006D full `childsum` — PASS.
   - T006E `firstrootsum` — PASS.
   - T006F Fernández–Procacci rooted-tree enumeration interface — EXTERNAL-INTERFACE PASS.
   - T006G final assembly — PASS.
   - Run #31: Lean job **SUCCESS**, PDF job **SUCCESS**, final outcome gate **SUCCESS**.
   - Raw `#print axioms`: no `sorryAx`; only `propext, Classical.choice, Quot.sound`.
   - External scope is limited to Fernández–Procacci, CMP 274 (2007), §4.1,
     Propositions 7–8 and equations (4.12)–(4.19): finite-height rooted-tree
     enumeration/factorial normalization and monotone all-height limit.
   - All YM-specific estimates, constants, contact counting, KP smallness,
     recursion bound, and first-root estimate are internal Lean proofs.

Next logical node:
`lem:root` → `lem:U2-source-analyticity` → `thm:U2`.


## Root-not-bulk-entropy decomposition

- `T007A_RootEntropy_DistanceExtraction.lean` — **PASS**.
- `T007B_RootEntropy_PenroseRootFactor.lean` — **PASS over Penrose external interface**.
- `T007C_RootEntropy_TsumComparison.lean` — **PASS**.
- `T007D_RootEntropy_FullAssembly.lean` — **PASS**.


## Newly closed theorem node

9. U2 `lem:root` (root does not enter bulk placement entropy) — **CLOSED / LEAN-CERTIFIED OVER PENROSE EXTERNAL INTERFACE**.
   - T007A distance/exponent extraction — PASS.
   - T007B Penrose + bounded external-root factor — PASS over exact Penrose interface.
   - T007C nonnegative `tsum` comparison — PASS.
   - T007D final `C_root` assembly — PASS.
   - Full run #35 final gate: **SUCCESS**.
   - Raw `#print axioms`: no `sorryAx`; only standard
     `propext, Classical.choice, Quot.sound`.
   - External roots contribute only `K_r^2`; no root variable enters the
     bulk polymer placement sum.
   - Analyticity is deliberately deferred to `lem:U2-source-analyticity`.

Next logical node:
`thm:U2` → `lem:distance` → `lem:supergeom`.


## Source-analyticity decomposition

- `T008A_SourceAnalyticity_FiniteClusterEntire.lean` — **PASS**.
  Scope: finite-cluster entire structure and zero-source identities.
- `T008B_SourceAnalyticity_FrechetDerivative.lean` — **PASS**.
  Scope: explicit complex Fréchet derivative on `ℂ × ℂ` and scalar source bounds.
- `T008C_SourceAnalyticity_TsumEngine.lean` — **PASS**.
  Scope: joint Banach-space differentiability of the `tsum` via
  `hasFDerivAt_tsum_of_isPreconnected`; this is genuinely joint in `ℂ²`.
- `T008D_SourceAnalyticity_PolydiscAssembly.lean` — **PASS**.
  Scope: open/preconnected polydisc and uniform M-test.
- `T008E_SourceAnalyticity_DerivativeMajorant.lean` — **PASS**.
  Scope: explicit derivative majorant and summability interface.
- `T008F_SourceAnalyticity_FullAssembly.lean` — **PASS**.
  Scope: final joint Fréchet-holomorphic + closed-polydisc uniform-convergence assembly.

## Newly closed theorem node

10. U2 `lem:U2-source-analyticity` — **PASS / LEAN-CERTIFIED**.
   - Fast A–E gate run #18: **SUCCESS** after the T008B canonical-lambda repair.
   - A–F gate run #20: **SUCCESS**.
   - Full synchronized verification run #58 (run id `36305245476`):
     Lean logical-order job **SUCCESS**, CURRENT/v128 PDF sync **SUCCESS**.
   - Raw `#print axioms` for all T008A–T008F certificates:
     only `propext, Classical.choice, Quot.sound`; no `sorryAx`.
   - CURRENT TeX now defines the continuous-linear projections,
     the explicit cluster Fréchet derivative, the derivative tree majorant,
     the smaller-polydisc M-test, and the exact joint `ℂ²` Fréchet-holomorphy meaning.
   - Static manuscript audit after synchronization:
     499 labels / 499 unique labels, duplicate labels = 0,
     missing refs = 0, forward refs = 0; vague shorthand scan = 0.
   - No genuine mathematical proof gap was opened at this node.
   - The implementation failures in the earlier T008B/T008E retries were
     product-instance/elaboration and implicit-argument issues only.

Next logical node:
`thm:U2` (marked-shell theorem) → `lem:distance` → `lem:supergeom`.


## Run #40: U2 → U3 → B08 synchronized batch

Head: `279a29531d46b166165c2d81eea6120a0f415a1a`.

- `thm:U2`: T009A/B/B-extraction/C — **PASS**.
- `lem:distance`: T010A full recurrence/geometric-tail theorem — **PASS**.
- `lem:supergeom`: T010B full finite supergeometric sum — **PASS**.
- U3-A UV covariance sum: T010C full finite-scale assembly — **PASS**.
- corrected clock cancellation/telescoping/path remainder/derivative/inverse-square prefix bound: T011A–T011E — **PASS**.
- `lem:B08-collar`: T012A full-state finite-horizon collar over the published preservation interface — **PASS**.
- `cor:B08-endpoint-cont`: T012B — **PASS**.
- `lem:B08-sign`: T012C — **PASS**.
- `lem:B08-IVT`: T012D — **PASS**.
- `lem:B08-first-exit`: T012E — **PASS**.
- `thm:B08-phaselock`: T012F — **PASS**.
- local-to-global guardrail T900 — **PASS**.

Fast run #40 and full synchronized run #40 both have final gate **SUCCESS**.
For every theorem printed in this batch the raw axiom audit contains only
`propext, Classical.choice, Quot.sound`; no `sorryAx`.
The repository privacy guard also reports no tracked `paper/`, `*.tex`, or `*.pdf`.

Next strict mathematical node:
`I7-GLOBAL-ROOT-FRAME`.
Downstream `thm:gramtotransfer`, `thm:gap`, and unconditional `thm:UIclosure` are blocked until that node is proved rather than assumed.
