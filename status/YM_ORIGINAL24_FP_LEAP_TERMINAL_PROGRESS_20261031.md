# YM-closed Original24 LEAP terminal closure ledger — 2026-10-31

## Honest manuscript ledger

- Historical conditional original-environment union: 37/39 = 94.87%; original 24 and 30 unverified.
- I7 remains an EXPLICIT UNPROVED GLOBAL HYPOTHESIS, not a physical Yang–Mills mass gap proof.
- All receipts are genuine fixed Lean 4.35.0-rc3, Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee, warnings-as-errors, exact #print type and #print axioms.
- No custom axioms / sorryAx: only propext, Classical.choice, Quot.sound.

## Existing strict four-node EXACT physical graph/combinatorics main chain

1. #41126077332 (9007/9007): original24_exact_graph_embeds_single_q.
2. #41126614284 (9009/9009): original24_exact_spanning_tree_to_single_q.
3. #41127177228 (9010/9010): original24_exact_tree_count_le_single_q.
4. #41128105206 (9017/9017): original24_exact_two_root_weighted_tree_le_single_q.

These are TRUE 4D periodic root and polymer source graphs; n bulk vertices plus p and q; q can branch, and n! is unchanged.

## New strict n=1 first coefficient and SHORT all-height KP route

5. #41129277001 (9019/9019): original24_FP_one_bulk_connected_from_KP.
   The actual one-polymer two-root contact contribution is bounded by exp(F_{h+1})-1 with h>=0 and cGeo*mu>=0, NO hFP input.

6. #41131396248 (9023/9023): exact source n=1 graph connected iff one bulk polymer contacts both physical Wilson roots; fixed-q factorial absorption:
     lambda^n*eps*w/n! <= (2lambda)^n*eps*w/(n+1)!
   for n>=0, w>=0, lambda,eps>=0;
   original24_fixed_q_factorial_absorbed strict Lean.
   This uses n+1 <= 2^n (proved) and therefore avoids an exact q label-orbit enumeration.

7. #41131396248 (9023/9023): original24_fixed_q_doubled_bulk_KP_from_U1,
   stronger weak-coupling 8B*aAct<=delta, delta=kappa-cGeo*mu>0,
   B=(2chi+1)^4, E=exp(kappa*|rootQ|):
     lambda=delta/(8B*aAct)
     epsilon=delta/(8B*E)
     (lambda*epsilon) * (64B^2 E aAct/delta^2)=1.
   True all-height finite KP root-forest estimate with the original bulk activity doubled. This is a genuine positive KP bound, NOT YET the full labeled-tree generating function.

8. NEW #41133232384 (9025/9025):
   original24_old_new_U1_factors_tendsto_zero and
   original24_old_new_FP_margin_from_decay.
   Assuming the physically standard yet currently EXTERNAL hypotheses
     kappa0>0 and p0(g)->+infinity as g->0+,
   we construct ONE gStop>0 with gStop<=gMax such that all 0<g<=gStop obey
     8 B [CR g^kappa0 Ccount] <=delta,
     8 B [CRnew exp(-p0(g)) Ccount] <=delta.
   This proves BOTH old/new FP quantitative margin inequalities as conclusions, not hsmall assumptions.
   The U1PublishedHypotheses structure alone does NOT currently include positivity of kappa0 and the p0 asymptotics; the actual CMP input must establish those separately.

CI references:
- https://github.com/penghongzhong/YM-closed/actions/runs/41129277001
- https://github.com/penghongzhong/YM-closed/actions/runs/41131396248
- https://github.com/penghongzhong/YM-closed/actions/runs/41133232384

## Shortest OPEN RED NODES (no artificial pass count)

A. True all-order nonnegative labeled-tree/exponential formula (FP Proposition 7, Equations 4.19--4.22):
   prove finite-height, source-class exact coefficient inequality mapping
   positive actual single-q rooted labeled spanning-tree weights, with q occurring ONCE,
   to exp(F_h(p;lambda*z,epsilon*q))-1.
   Use the checked fixed-q n+1 <= 2^n adjustment if it shortens the Lean proof;
   correct geometric sign cGeo*mu>=0 and full finite-height label range matter.
   NO presumed PhysicalExactTwoRootFPCriterion as a terminal assumption.
B. Actual CMP119/CMP122 Bałaban unmarked old/new R history-to-hard-core-polymer and U1 support/length/background dictionary at the SAME physical regulator and RG level, with 4D shell count.
C. The physical sourceLift, canonical a^(4-d) jet/counterterm matching and B10 fifth-order weak-source Taylor scale gain, uniformly in actual cutoff/volume.
D. Compile the unchanged meaningful original24 B11 finite-D source-class theorem with (A)--(C) supplied by valid previous inputs. ONLY THEN 38/39.
E. Original30 genuine RENORMALIZED joint Schwartz E0' all orders, separate and still open.

Published FP: Fernández--Procacci, Commun. Math. Phys. 274 (2007), 123--140.
No preprint/publication proof substitutes for a completed model-specific Lean theorem unless deliberately used as a transparently named external published interface.

Current branch: ym-original24-fp-enumeration-20261031.
Main/default branch unchanged.
