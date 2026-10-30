# YM-closed Original24 exact two-root FP finite-graph proof chain — 2026-10-31

## Official strict pin and latest acceptance

Public repository: penghongzhong/YM-closed
Isolated branch: ym-original24-fp-graph-20261031
Lean: leanprover/lean4:v4.35.0-rc3
Mathlib: 516d31250e96c4e8e76888c3d8e2e43a9642b9ee
All claimed strict receipts below use real GitHub-hosted pinned builds,
-DwarningAsError=true, full theorem types and #print axioms.
No sorryAx, sorry, admit or custom axioms in the audited terminal declarations;
only propext, Classical.choice, Quot.sound.

1. Actions #41126077332 — SUCCESS, 9007/9007
   YMOriginal/Original24_ExactGraphToSingleQ.lean
   original24_exact_graph_embeds_single_q
   Exact edge embedding of the original n+2 vertex two-root Mayer graph
   into the one-q-species, p-rooted graph, with the SAME actual periodic
   hard-core supports, allowing q to branch. A possible augmented
   direct p-q contact is only an extra positive overcount, never an equality.
   Ported prior official source exact q contact and 1/n! factorial results.

2. Actions #41126614284 — SUCCESS, 9009/9009
   YMOriginal/Original24_ExactTreeTransport.lean
   original24_exact_spanning_tree_to_single_q
   Transport every full original labeled spanning tree via the exact
   vertex equivalence to a spanning tree of the augmented graph.

3. Actions #41127177228 — SUCCESS, 9010/9010
   YMOriginal/Original24_ExactTreeCount.lean
   original24_exact_tree_count_le_single_q
   For every actual periodic regulator, finite bulk tuple, and sources,
   #ST(G_exact(tuple)) <= #ST(G_aug(tuple)), proved via an
   injective subtype map, not a conjectured tree cardinality input.

4. Actions #41128105206 — SUCCESS, 9017/9017
   YMOriginal/Original24_ExactWeightedTreeComparison.lean
   original24_exact_two_root_weighted_tree_le_single_q
   The SAME actual finite polymer activity z, SAME n+2 graph, SAME
   labeled tuple and SAME symmetry factor 1/n! yield
      exactExtendedTwoRootTreeMajorant(n,...) <=
      actualSingleQWeightedTreeMajorant(n,...).
   This is an actual positive, coefficient-weighted Mayer majorant,
   not an assumed hFP or abstract arbitrary scalar tree family.

CI references:
https://github.com/penghongzhong/YM-closed/actions/runs/41126077332
https://github.com/penghongzhong/YM-closed/actions/runs/41126614284
https://github.com/penghongzhong/YM-closed/actions/runs/41127177228
https://github.com/penghongzhong/YM-closed/actions/runs/41128105206

## What is STILL unproved (do not promote Original24)

**Historical conditional manuscript-original union remains 37/39 (94.87%).**
Original 24, 30 are not accepted as complete original manuscript environments.
I7 is an unproved global theorem hypothesis. No unconditional mass-gap claim.

The remaining exact mathematical FP combinatorial node is the
*ALL-n finite-height weighted exponential enumeration* of the one-q
augmented rooted forest, not its finite graph embedding or coefficient
tree-count majorization. For every h, λ>=1 and ε>0, prove an inequality
of the following schematic exact-form type:

  sum_(1<=n<h-1) λ^n ε / n! *
    sum_(tuple : Fin n -> Γ)
       #ST(G_aug(tuple)) * product_i ||z(tuple_i)||
      <= exp(actualPeriodicFirstRootSum(h; λ*z, ε*q)) - 1.

The actual right-hand recursion uses polymer vertex weights
  ||z(X)|| exp(cGeo*mu*d(X)),
  ε exp(cGeo*mu*|rootQ|), with positive physical μ,cGeo.
The current generic PhysicalExactTwoRootFPCriterion type has NO sign
assumption on cGeo*mu; proving it for arbitrary real values is not valid.
The physically justified positive-parameter specialization must be made
explicit, and the one-q labeled exponential species/tree enumeration
proved with exact finite-height truncation and correct factorials.
Do not pass the desired model-specific hFP bound as a new axiom.

Independently, show that CMP119/CMP122 genuine Balaban old/new-R
large-field histories are the SAME hard-core polymer species, with
native supports/lengths, contact graph, root insertion, finite-history
weight, background, RG level and all-regulator uniformity. Current
U1Data is an interface, NOT this physical identification.

Finally establish actual weak-coupling quantitative margin and fixed-D
jet / a^(4-d) canonical source normalization / fifth-order marked B10
localization / B09 mixing source dictionary, then compile the **unchanged**
Original24 full source-class theorem to promote 37/39 -> 38/39.

All new proof files are in one isolated branch; default main remains unchanged.
