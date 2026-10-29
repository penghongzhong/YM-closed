# 2026-10-29 Yang–Mills U–I–C, Original 30: public Lean handoff

Public branch: `ym-original30-public-20261029`. The repository `main` branch remains unchanged.

## Fixed verification toolchain
- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
- Theorems were compiled on GitHub-hosted Linux runners, with explicit `#print axioms` verification.

## New public strict verification records
1. [40845898253](https://github.com/penghongzhong/YM-closed/actions/runs/40845898253): **success**; two standalone scaled-shell arithmetic proof modules.
2. [40846684410](https://github.com/penghongzhong/YM-closed/actions/runs/40846684410): **success**; six exact-source Schwartz derivative modules and the two earlier arithmetic lemmas.
3. [40847113878](https://github.com/penghongzhong/YM-closed/actions/runs/40847113878): **success**; the ten-module Fourier derivative/summability dependency closure, the six-module Schwartz closure and the two arithmetic modules.

All three runs actually allocated GitHub runners, downloaded the locked Mathlib dependencies, compiled the targeted modules and completed the axiom check. The last run prints standard foundations only:
`[propext, Classical.choice, Quot.sound]` for the six audited root/bridge theorems.

## Exact scope, no numerator inflation

New or transferred public files: **18 Lean files** = two new arithmetic theorems + six existing Schwartz modules + ten existing Fourier modules.

The retained manuscript ledger from the active private research branch stays:
- standard-input-assisted conditional: **34/39**;
- native conditional implications: **31/39**;
- union of historical/official pin per-environment reports: **24/39**;
- pending originals: **1, 24, 30, 34, 42**;
- **I7 remains unproved** and full mass-gap/U–I–C proof is not closed.

These files verify components of Original 30, **not the complete original manuscript environment**. An external theorem parameter or actual Wilson premise has not been turned into an axiom or silently counted as proved.

## Remaining shortest-path obligations
1. Construct the actual normalized cutoff/scaling/periodization for a `SchwartzMap (EuclideanSpace ℝ (Fin (4*r))) ℂ`, including the mixed derivative chain expected by `fourier_mixed_c2_summability`.
2. Prove the uniform Wilson local `C²` source seminorm bound and its `C²` Fourier reconstruction with exact smearing/root-support correspondence.
3. Derive the actual `analytic_coefficient_synthesis` scalar coefficient budget, pure-test factorization and same-filter limits, with all regulator-uniform constants and order quantifiers.
4. Reconcile the result with the original manuscript §17.5 OS `E0'` hypothesis before promoting Original 30.
5. Afterwards target Original 34 reconstruction and Original 42 assembly; no claim that I7 follows from these steps.

Private manuscript and private archive files have not been published in this transfer.
