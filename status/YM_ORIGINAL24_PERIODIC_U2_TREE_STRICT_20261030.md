# YM-closed: Original24 periodic physical U2 rooted-tree closure certificates — 2026-10-30

## Strict original manuscript environment ledger

**37/39 = 94.87%** remains the validated historical *conditional original environment* union;
full Original24 and Original30 remain **OPEN**.
I7 remains an **UNPROVED explicit theorem parameter**. It is not
included in the numerator and no new Lean axiom was introduced.

- Public repository: `penghongzhong/YM-closed`
- Branch: `ym-original24-link-wilson-20261030`
- Toolchain: Lean `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`
- Only standard foundational Lean axioms found:
  `propext`, `Classical.choice`, `Quot.sound`.
- **No sorry/admit/sorryAx/new axiom** in these new proofs.

## Newly certified rigorous bridge, 14 theorem declarations

1. [Official Actions #41002393417](https://github.com/penghongzhong/YM-closed/actions/runs/41002393417) **SUCCESS**,
   5 new theorems from two modules:
   - `YMOriginal/Original24_ActualRootContactCounting.lean`
     builds actual physical root contact and support-covering families and
     **derives** the U2 first-root bound from the original U1
     unmarked *per-block* analytic activity norm; the root sum is NOT
     a premise.
   - `YMOriginal/Original24_PeriodicFourDimContact.lean`
     constructs literal periodic 4D `Fin 4 -> ZMod N` offsets and proves
     `|Neighbour_chi(site)| <= (2chi+1)^4` independent of N, and hence
     `sum_{X contact root} w(X) <= (2chi+1)^4 |root| aAct`.
2. [Official Actions #41002966674](https://github.com/penghongzhong/YM-closed/actions/runs/41002966674) **SUCCESS**,
   2 new theorems:
   - `YMOriginal/Original24_PeriodicKPFiniteTree.lean`.
     Under `delta=kappa-cGeo*mu>0` and
     `(2chi+1)^4*aAct <= delta/2`, derives the finite
     KP child-barrier estimate from the actual 4D local U1 norm;
     proves the recursively defined tree bound
     `F_h(X) <= exp(delta*d(X)/2)` for **every h**.
     No `hchild` nor marked tree bound appears as a hypothesis.
3. [Official Actions #41003034332](https://github.com/penghongzhong/YM-closed/actions/runs/41003034332) **SUCCESS**,
   1 new theorem:
   - `YMOriginal/Original24_OnePolymerTwoRootReal.lean`.
     The true periodic one-polymer bridge, touching both actual
     Wilson-root neighborhoods, has the exponentially damped
     two-root source bound derived from local U1 and native
     one-polymer root distance. This is ONLY the single-polymer
     case, not the full multi-polymer connected Ursell expansion.
4. [Official Actions #41003396609](https://github.com/penghongzhong/YM-closed/actions/runs/41003396609) **SUCCESS**,
   3 new theorems:
   - `YMOriginal/Original24_PeriodicRootTreeLimit.lean`.
     Proves monotonicity of finite-height trees, a height-uniform
     first-root sum, and a genuine **infinite-height limit**
     `F_h^root -> F_inf^root <= (2chi+1)^4 |root| aAct`;
     does not assume a convergent infinite root tree.
5. [Official Actions #41003625924](https://github.com/penghongzhong/YM-closed/actions/runs/41003625924) **SUCCESS**,
   3 new theorems:
   - `YMOriginal/Original24_ActualWilsonRootFamilySupport.lean`.
     For a finite family of M actual CLOSED lattice Wilson loops
     with at most L links each, derives
     `|root support| <= M*(L+1)` directly from true link-path
     vertex lists. Thus the root contact budget is
     `(2chi+1)^4 * M*(L+1) * aAct`,
     uniform in physical volume and UV cutoff; Nroot is no longer
     an arbitrary geometry hypothesis.

**All five successful workflows checked full Lean declarations and
`#print axioms`; the 14 declarations are NOT 14 additional original
manuscript environments.**

## Previous original24 proofs on the same branch

- Exact sitewise SU2 link holonomy and full gauge invariance:
  [#40990364337](https://github.com/penghongzhong/YM-closed/actions/runs/40990364337)
- True two independent external Wilson roots with mixed-source subtraction:
  [#40996554264](https://github.com/penghongzhong/YM-closed/actions/runs/40996554264)
- Full arbitrary source radius `exp(rBp)-1`, `exp(rBq)-1`;
  physical fixed template support geometry:
  [#40998298304](https://github.com/penghongzhong/YM-closed/actions/runs/40998298304)
- EXACT previously audited Bałaban U1 published old/new-R
  coefficient/histories applied to actual SU2 two-root external
  insertions:
  [#40998329180](https://github.com/penghongzhong/YM-closed/actions/runs/40998329180)
- Previously audited B10 fifth-order Taylor and 4D placement-ratio
  certificates are preserved unchanged.

## Narrow critical path to *genuine* complete Original24

1. Prove that the real C29 CMP119/CMP122 *connected polymer histories*
   are exactly the already modeled periodic graph/polymer contact and
   support/length objects, including proper source attachment
   and the same rooted native distance, not a surrogate distance.
2. Establish the **Ursell/Penrose and Fernández–Procacci**
   labeled-rooted-tree identification:
   the real connected-cluster majorant must map to the proved
   infinite-height KP rooted recursion, including the two-root
   support subfamily and all factorial/symmetry factors. The
   just-proved infinite KP recursion is NOT automatically the
   physical connected cumulant sum.
3. Transfer the resulting true old/new-R marked cluster estimates
   to the SAME finite-D source jet projection and fourth-order
   B10 localization and to the earlier Original19 finite-dimensional
   source cocycle, with canonical powers managed by counterterms
   instead of small coupling.
4. Only after the UNCHANGED Original24 `C-LOCAL-POLY-LFD=CLOSED`
   claim is fully modeled, compiled, typechecked and axiom-audited
   may the original environment count be promoted to 38/39.

## Remaining Original30 model/analytic obstacles

The real all-volume bare Wilson moments do NOT establish the
canonically normalized renormalized D=4 curvature source, nor the
uniform RG source analytic chart, full JOINT 4r Schwartz
renormalized Schwinger hierarchy, same-net continuum limit, or
nontriviality. These remain open. The current historical 37/39
includes conditional/external-interface environment passes,
not an unconditional proof of the Clay Yang–Mills mass gap.

## External source audit notes

Bałaban CMP119 (1988) is an effective-density and R-inductive
description and does not itself directly provide arbitrary
composite-source differentiation. The separate large-field
R-operation bounds for four-dimensional pure lattice gauge theory
are in Bałaban CMP122-I/II (1989).
Exact source dictionary/equation matching should be checked
against the papers rather than inferred from a shared letter R:
- CMP119: https://doi.org/10.1007/BF01217741
- CMP122-II: https://doi.org/10.1007/BF01238433
