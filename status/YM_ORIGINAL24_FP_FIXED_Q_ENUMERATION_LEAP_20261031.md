# Original24 fixed-q FP shortest-chain LEAP audit — 2026-10-31

## Strict real Lean acceptance

Repository: penghongzhong/YM-closed
Isolated branch: ym-original24-fp-enumeration-20261031
Source commit: f834fb58e507bd42cc8b9ea570515d767bb6b0e9
Pinned Lean: leanprover/lean4:v4.35.0-rc3
Mathlib: 516d31250e96c4e8e76888c3d8e2e43a9642b9ee

GitHub Actions #41131396248 SUCCESS.
Actual `lake build` 9023/9023. Warning-as-error Lean replay plus FULL
`#print` theorem types and `#print axioms` for all four terminal names
succeeded; axioms only propext, Classical.choice, Quot.sound. No
sorryAx/admit or newly declared axioms in this acceptance.

All four are in the actual physical periodic SU(2) polymer
source context, except the purely numerical factorial inequality.

1. `YMOriginal/Original24_FPFirstConnectedBulk.lean`:
   `original24_FP_one_bulk_connected_from_KP`.
   For bridge = polymers contacting BOTH actual Wilson-root supports,
   and 0<=cGeo*mu, lambda>=1, eps>0, prove for ALL h:
     lambda*eps*sum_(X in bridge)||z(X)||
       <= exp(actualPeriodicFirstRootSum(h+1;lambda*z,eps*q))-1.
   No hFP or direct connected-series bound among theorem assumptions.

2. `YMOriginal/Original24_FPFirstGraph.lean`:
   `original24_exact_one_bulk_graph_connected_iff`.
   The actual n=1 full three-vertex Mayer graph is connected IFF its
   unique bulk vertex contacts BOTH physical Wilson roots. This aligns
   the n=1 KP contribution with the original source graph.

3. `YMOriginal/Original24_FPFixedQFactorial.lean`:
   `original24_succ_le_two_pow`, `original24_fixed_q_factorial_absorbed`.
   n+1<=2^n for every natural n and, for lambda,eps,w>=0,
     lambda^n eps w/n! <= (2lambda)^n eps w/(n+1)!.
   This completely removes the need for an exact q-label orbit-factorial
   identity IF one is willing to pay a doubled bulk fugacity in a
   universal positive rooted-tree enumeration.

4. `YMOriginal/Original24_FPFixedQForest.lean`:
   `original24_fixed_q_doubled_bulk_KP_from_U1`.
   B=(2chi+1)^4, E=exp(kappa*|rootQ|),
   delta=kappa-cGeo*mu>0, aAct>0.
   Under 8*B*aAct<=delta and the genuine unmarked per-block U1 norm,
   derive lambda>=1, eps>0, with
     (lambda*eps)*(64*B^2*E*aAct/delta^2)=1
   and the ACTUAL all-height augmented KP forest bound
     exp(F_h(p;lambda*(2*z),eps*q))-1
       <= exp(|rootP|*delta/2)-1
   for EVERY h (no hFP input). This is a logically stronger
   weak-coupling requirement than the previously used 4B*aAct<=delta.

Previous certified finite-graph chain, separately:
- #41126077332 real two-root to single-q graph edge embedding.
- #41126614284 spanning-tree transport.
- #41127177228 spanning-tree count inequality.
- #41128105206 exact coefficient-weighted tree inequality, same 1/n!.

Previous fixed-D source/cocycle quantitative terminal:
- #41123878633 strictly compiled; exact physical FP criterion still
  explicit as a theorem input; does NOT include fifth-order scale gain.

## RED mathematical nodes — do NOT claim completed Original24

R1: ALL-n universal Fernandez–Procacci positive labeled
rooted-tree-to-KP exponential enumeration, with fixed q in one slot,
an exact finite-height height n+2 and no root-root Mayer edge.
The proved factorial bound gives the precise safe shortcut:

  sum_{n=1}^{h-2} lambda^n*eps/n! *
    sum_(tuple : Fin n -> Gamma)
      #ST(G_exact(tuple)) * prod_i ||z(tuple_i)||
    <= exp(F_h(p;2lambda*z,eps*q))-1,

but this ALL-n inequality is NOT YET KERNEL-PROVED.
The graph-to-augmented-tree dominance, n=1 case, doubling and
independent all-height KP bound ARE proved.
The cited generic FP theorem is for hard-core incompatibilities;
a genuine exact instantiation is required, not a renamed hFP premise.

R2: Show actual CMP119/CMP122 Bałaban R-history variables match
the literal finite hard-core polymer species, support, distance,
Mayer graph, sources and activity coefficients uniformly in
cutoff, volume, RG level and background. U1Data remains an
external model interface, not a constructed identification.

R3: Derive strong 8B*aAct<=delta in the actual weak-coupling
window from precisely typed kappa0>0, p0(g)->infinity, published U1
uniform shell geometry and zero-activity cases. Those positivity
and limiting hypotheses are absent from current U1PublishedHypotheses
and must not be silently inferred.

R4: Physical fixed-D normalized source jet, engineering
a^(4-d), fifth-order marked B10 localization, B09/Original19 mixing
and actual post-R norm match to unchanged Original24 manuscript.

Historical conditional original-environment PIN receipt union
37/39=94.87%. IDs 24 and 30 still OPEN; count is NOT promoted based
on helper or terminal under explicit external conditions.
I7 remains explicitly UNPROVED. No unconditional four-dimensional
SU(2) Yang–Mills mass-gap or continuum construction is claimed.

## Receipts
https://github.com/penghongzhong/YM-closed/actions/runs/41129277001
https://github.com/penghongzhong/YM-closed/actions/runs/41131396248
https://github.com/penghongzhong/YM-closed/actions/runs/41128105206
