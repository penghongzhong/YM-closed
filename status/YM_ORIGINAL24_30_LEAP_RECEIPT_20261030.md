# YM Original24/30 LEAP strict receipt — 2026-10-30

Repository: penghongzhong/YM-closed
Branch: ym-original24-30-rooted-poly-20261030
Inherited base: 98ded0de6bf8a2571e04bedc96129df1c8146d10
Latest compiled source/workflow commit: b88acbbef054b540b29cde275cbd42c98e9ea6da
Lean 4.35.0-rc3; Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

## Strict acceptance

Latest success: https://github.com/penghongzhong/YM-closed/actions/runs/41012752678
Previous successes: 41011105603, 41011642333, 41012008903, 41012236958, 41012524244.
The workflow runs the full module build, Lean warning-as-error, prints complete theorem statements and prints axioms. Only standard propext, Classical.choice and Quot.sound occur; zero sorryAx and no custom axioms.

## Original24 new formally checked modules

YM/Wilson/CompositeWordPolynomial24.lean
- Actual noncommutative ordered SU(2) Wilson-word products and finite complex polynomial observables, rather than only a Gram-root surrogate.
- Exact coefficient budget B = sum_t ||coeff_t|| 4^(number of factors), giving ||R(U)|| <= B.
- ||exp(s R(U))-1|| <= 2 ||s|| B when ||s|| B <= 1.
- For any fixed radius r and regulator-uniform budget, ||exp(sR(U))-1|| <= exp(rB)+1 for ||s|| <= r.
- Schwartz test evaluation bounded by B p_00(f).

YM/Wilson/CompositeWordDirection24_30.lean
- The whole actual finite-volume source vector built from the SAME SU(2) configuration.
- ||J_{a,U}(f)||_ell∞ <= B p_00(f), independent of the number of root/source sites, given the stated budget.
- Exact subtraction, Lipschitz estimate and all-regulator quantifiers.

Original24 NOT YET CLOSED. Still require: the paper's fixed-D jet/source normalization dictionary and regulator-independent coefficient budget; actual marked large-field old/new R activities through U2 rooted tree enumeration; fifth-order marked R-sector remainder bound; B09 counterterm inverse cocycle and canonical a^(4-d) bookkeeping.

## Original30 new formally checked modules

Inherited generic already-verified Mathlib files from companion private project, selectively ported without paper text: YM/OSGrowth/Moments, Polymer, PolynomialRadiusBound, PolynomialMomentGrowth, RootCoverCount and YM/OSTensor/MaxShellMoment.

YM/OSGrowth/Original30PolynomialPolymerGrowth.lean:
Finite analytic polymer log, uniform activity decay and finite root count imply single-factorial growth with polynomial dependence on root support.

YM/OSTensor/Original30RootedMaxShell.lean:
Four-dimensional maximum-shell count C 2^(4N) exp(σk) yields moment cost O(2^(4rN)) with r!.

YM/OSTensor/Original30RootCoverMaxShell.lean:
The global count follows from a finite root cover, a per-root level count, and ||K_N|| <= H 2^(4N); global counting is derived, not postulated.

For A = ε H B/(1-exp(-(κ-σ))) and κ > σ, the strict assembly yields

 ||D^r exp(W(J)-W(0))|_(J=0)[h_1,...,h_r]||
 <= exp(1) * (2 exp(1) (1+A)/ρ)^r * r! * 2^(4rN) * product_j ||h_j||.

Earlier certified Fourier-Schwartz shell budget supplies 2^(-5rN), producing total 2^(-rN) decay after the 2^(4rN) moment cost.

Original30 NOT YET CLOSED. Still require: exact analyticity/decay of physical RG-renormalized SU(2) Wilson polymer activities with uniform radius; B08 fixed-physical-scale root cover; actual C² normalized source jets, Schwartz/Fourier periodization and assembly; full cutoff-volume weak-stop continuum limit.

CRITICAL: If root cover K_N indexes raw UV plaquettes, its cardinality scales as a^(-4) 2^(4N), not O(2^(4N)) uniformly. Must use physical-scale blocks or weighted covering; the model assumption has NOT been proved.

## Honest original environment accounting

CURRENT HISTORICAL PER-ORIGINAL-ENVIRONMENT OFFICIAL-PIN CONDITIONAL UNION:
37/39 = 94.87%. Only original 24 and 30 remain open.
The old 34/39 was the 2026-10-29 baseline, BEFORE additional #1
(exact published U1 external interface), #42 (conditional I7 master)
and #34 (conditional published OS-II reconstruction interface) were
strictly compiled on other YM-closed public branches on 2026-10-30.
Reference official ledger:
- status/YM_I7_CONDITIONAL_01_42_20261030.md on branch
  ym-original01-42-i7-conditional-20261030;
- status/YM_ORIGINAL34_37_AND_ORIGINAL30_INPUTS_20261030.md on branch
  ym-original34-exact-os-20261030.
This is a UNION of separate historical strict Lean receipts, not a new
monolithic all-37 build on this isolated branch. Original #1 and #34
use published external interfaces, while #42 is conditional on I7 and
the stated model/passage premises. I7 remains OPEN and no unconditional
Yang--Mills mass-gap or fully physical model proof is claimed.
None of the new supporting statements in this branch is promoted to an
original manuscript theorem environment.

## Next minimal burden

24: actual Wilson root -> fixed-D normalized jet dictionary -> U2 marked post-R activity -> five-order localization and B09 cocycle -> exact original24 statement.
30: actual analytic RG source chart and fixed-scale cover -> max-shell factorial estimate -> actual C² Wilson source/Fourier dictionary -> joint continuum Schwartz limit -> exact original30 statement.

Proof sources and audit are all preserved in this isolated public branch.
