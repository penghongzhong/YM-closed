# Original24 → 38/39: exact physical double-root terminal receipts and remaining obligations
Date: 2026-10-30

## STRICT verified proof receipts

Public repo penghongzhong/YM-closed.
Branch ym-original24-real-two-root-fp-20261030.
Official pin leanprover/lean4:v4.35.0-rc3; Mathlib
516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

- Actions #41038072394: SUCCESS (9011/9011).
  New: YMOriginal/Original24_ExactRealTwoRootFPSeries.lean
  Declarations:
    actual_exact_two_root_positive_tree_weight
    PhysicalExactTwoRootFPCriterion (an explicit UNPROVED model/input condition)
    actual_original24_two_root_mayer_full_sum_from_U1_FP
  The last theorem derives from actual ORIGINAL physical n+2-vertex
  Mayer--Ursell and rooted spanning-tree coefficients:
    (i) absolute summability of the full n>=1 connected
        SU2 Wilson source series;
    (ii) cutoff-independent O(aAct) norm upper bound.
  It does NOT assume an arbitrary Phi_n or an abstract Tree
  type among its physical full-series conclusions. It derives
  the sum bound from unmarked U1/KP, explicit strong margin and
  a precisely specified finite-height FP criterion on the
  actual labeled n+2-vertex source graph.
  Note the h-2 height shift for two distinct external vertices.

- Actions #41039177750: SUCCESS (9014/9014).
  New: YMOriginal/Original24_BalabanTwoRootRealFullSeries.lean
  Declaration:
    original24_balaban_real_old_new_complete_two_root_series
  Both oldR and newR are EXACT fields of the published
  U1Data at the SAME RG level, background, native polymer
  species, length, support and physical periodic regulator.
  Per-block local U1 norms are DERIVED from pointwise Balaban
  old/new-R decay plus explicit UNMARKED finite-history count
  (the latter has NOT been proved uniformly for the native
  physical CMP119/122 histories).
  The theorem uses true actual SU2 closed lattice-link holonomies,
  true two-root Wilson word source insertions, and the actual
  connected Mayer 1/n! graph coefficient. Under the exact
  external combinatorial FP input, it proves BOTH original
  sectors' full n>=1 connected source series absolutely summable
  with actual O(aAct_old/new) bounds.
  The n=0 connected coefficient is identically zero, as
  separately certified by Original24_ExactTwoRootAttachment.lean.

Both workflows used an actual pinned full Lean module build,
-DwarningAsError=true, full #print of theorem types and
#print axioms of terminal declarations. Only core
propext, Classical.choice, Quot.sound; no sorryAx or custom axioms.

CI links:
https://github.com/penghongzhong/YM-closed/actions/runs/41038072394
https://github.com/penghongzhong/YM-closed/actions/runs/41039177750

## Why this is NOT yet 38/39

Historical per-original-environment conditional union remains
37/39=94.87%; only IDs 24 and 30 remain open. I7 is still
an explicit UNPROVED global premise; there is no established
unconditional 4D SU2 continuum mass gap.

Original24 manuscript label:
  thm:B11-repair
  C-LOCAL-POLY-LF_D=CLOSED (for each finite fixed D).
The actual B11 source-jet/regulator-uniform model theorem is
NOT what the latest new declarations state, and must NOT be
registered as certified by adding a tautological closure label.

Remaining precise ORIGINAL24 mathematical obligations:

1. Prove PhysicalExactTwoRootFPCriterion for the ACTUAL
   fixed-D n+2-vertex Wilson--Mayer graph. This is the
   finite-height 1/n! Penrose-to-Fernández--Procacci
   planar-tree enumeration with one q vertex, n>=1 bulk
   vertices, possible q branching, no root-root edge.
   The published 2007 theorem is for hard-core
   incompatibilities; applying it to arbitrary soft
   interactions is not justified. The Lean criterion is
   currently a theorem PARAMETER, not a Lean result.

2. Prove that the actual CMP119/CMP122 large-field
   R-history representation IS the chosen hard-core
   periodic polymer gas with precise graph, source
   insertion, native support and distance, across all
   cutoffs, volumes, backgrounds and weak-stop scales.
   The existing U1Data structure and finite Γ are interfaces,
   not a native indexed construction of this physical map.
   In particular derive its cutoff/volume-uniform UNMARKED
   per-block history count Ccount, not merely assume it.

3. Transport actual native root-distance exponential moments
   to the exact 4D Schwartz fifth-order Taylor source
   localization, then identify the v122 fixed-D projection,
   canonical engineering factor a^(4-d), finite B09/Original19
   counterterm coordinates and the real post-R norm.
   Earlier Lean B10 and Original19 theorems are reusable
   but their source/function-space dictionary is not proved.

4. Check the stronger smallness 4(2chi+1)^4 aAct <= delta
   at the actual weak coupling scale from the published
   g_j^kappa and exp(-p0(g_j)) inputs, including the zero
   activity regime. This may require stronger hypotheses
   than the 37/39 historical source ledger.

If these steps are not completed, do not claim
Original24 passed / 38/39 or an unconditional proof.

## Source references

R. Fernández and A. Procacci, "Cluster expansion for abstract
polymer models. New bounds from an old approach," CMP 274
(2007), 123-140. Sec. 4, Eq. 4.12--4.15;
https://doi.org/10.1007/s00220-007-0279-2.

T. Bałaban, "Large field renormalization. II.
Localization, exponentiation, and bounds for the R
operation," CMP 122 (1989), 355-392;
https://doi.org/10.1007/BF01238433.
