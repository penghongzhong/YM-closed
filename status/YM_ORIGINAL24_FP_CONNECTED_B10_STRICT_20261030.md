# Original24 fast terminal LEAP acceptance — 2026-10-30

## Strict official toolchain

Public repo penghongzhong/YM-closed
Branch ym-original24-fp-terminal-20261030
Starting commit a8deb90ecc310032fb2c517ecde4e7a31d4528d8
Lean leanprover/lean4:v4.35.0-rc3
Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee

Verified Actions (full Lean compilation, theorem statements, #print axioms):
- 41019331717: https://github.com/penghongzhong/YM-closed/actions/runs/41019331717 — SUCCESS, 9000 jobs.
- 41020002863: https://github.com/penghongzhong/YM-closed/actions/runs/41020002863 — SUCCESS, 9002 jobs.
- 41020627217: https://github.com/penghongzhong/YM-closed/actions/runs/41020627217 — SUCCESS, 9006 jobs.

Only foundations propext, Classical.choice, Quot.sound occur in proof axiom audit. No sorryAx, sorry/admit or new axioms in accepted sources.

## Five newly strictly verified named theorem environments

1. YMOriginal/Original24_ConnectedUrsellFP.lean:
   original24_connected_ursell_from_periodic_FP.
   From actual 4D periodic U1 local activity + KP weak-source
   hypothesis + explicitly provided pointwise Penrose comparison +
   finite-height Fernández–Procacci labeled-tree counting, proves
   absolute convergence of the entire infinite connected Ursell
   series and its root-volume-independent bound. Its infinite
   summability and global root-sum bound are NOT theorem premises.

2. Same module:
   original24_actual_two_root_connected_ursell.
   Inserts genuine noncommutative SU2 ordered Wilson word polynomial
   roots at full finite source radius, and derives full connected
   cluster absolute sum and bound.

3. YMOriginal/Original24_FromPublishedU1ConnectedFP.lean:
   original24_real_U1_old_new_local_norm.
   Uses the REAL published original U1Data.oldR/newR coefficients,
   explicit native integer-distance compatibility and UNMARKED
   polymer history count to DERIVE the local block activity norms.

4. Same module:
   original24_real_U1_old_new_connected_Wilson.
   Instantiates the true Balaban old/new R fields at the SAME
   RG step/background, and actual site-link SU2 closed Wilson
   holonomies, rather than an arbitrary abstract complex z.

5. YMOriginal/Original24_ConnectedWilsonB10.lean:
   original24_connected_Wilson_B10_from_U1_FP.
   Proves for EVERY finite connected history truncation m the exact
   FOURTH-order Taylor subtraction and FIFTH-order remainder from
   (a) actual Schwartz(R4) source line fifth derivative;
   (b) weighted Penrose/FP finite-height linked-cluster estimate;
   (c) genuine full-radius two-root SU2 insertion.
   No hB10, independent fifth-moment estimate, full-series
   bound, or source-deformed large-field R analyticity is assumed.
   Bound: ||Rem_m|| <= (5 M / mu^5) Mf (aJ/aN)^5,
   where M = (exp(radius Bp)-1)(exp(radius Bq)-1)
      (2chi+1)^4 |root| aAct.

## Exact remaining ORIGINAL24 mathematical inputs

Do not inflate the historical original-environment count:
current union remains 37/39 = 94.87%, with ORIGINAL24 and ORIGINAL30 open.
These five verified declarations are NOT the unchanged original
manuscript B11/source-class environment. They still depend on:
- REAL C29/CMP119/CMP122 native polymer-history identification with
  the periodic polymer support/length and the connected Ursell
  coefficients (not merely a scalar surrogate);
- a proof or exact published source dictionary for the UNMARKED
  per-block history counting and the weighted Penrose/FP interface
  applied to those same original R histories;
- v122 fixed-D jet, canonical a^(4-d), B09 counterterm dictionary,
  and source-class localization after Taylor subtraction.
All must hold uniformly over the original regulator, cutoff, volume,
background and weak-stop range.
I7 is unchanged and UNPROVED as an independent theorem premise.
No unconditional SU(2) Yang–Mills mass gap is claimed.

## External bibliography for an exact theorem-source audit

- R. Fernández, A. Procacci, Commun. Math. Phys. 274 (2007), 123–140,
  https://doi.org/10.1007/s00220-007-0279-2; especially Penrose
  tree-graph identity and labeled rooted-tree recursion.
- T. Bałaban, Commun. Math. Phys. 122 (1989), 355–392,
  https://doi.org/10.1007/BF01238433; original large-field R bounds.
Both published results are currently *explicit hypotheses* in
Lean where their exact physical specialization has not been constructed.

## Next shortest closure

Construct and typecheck a SAME-history finite polymer/connected
Ursell coefficient dictionary from the actual old/new-R CMP122
activities, and prove the weighted Penrose/FP finite-height identities
for that dictionary; then transport the resulting marked B10
remainder into the unchanged fixed-D source jet / Original19
counterterm source map. Only then count 38/39.
