# I7 Round 59 — exact Wilson RG covariance and continuum-only vanishing-defect gap passage
Date: 2026-11-14
Branch: ym-i7-b14-vanishing-error-20261114
Baseline: historical 39/39 CONDITIONAL; physical I7 OPEN; no Clay mass-gap claim.

## A. Actual-model finite-volume identity, without treating old/new-R as the entire covariance

Let mu_a(dU) be the genuine SU(2) Wilson measure at cutoff a and finite volume, with the exact gauge-invariant action and OS reflection. Let K_a(dB|U) be a genuine RG blocking kernel (possibly deterministic). Require the exact original marginal:
  nu_a(dU,dB)=mu_a(dU)*K_a(dB|U),
  (pi_U)_*nu_a=mu_a.

For any square-integrable X,Y of U (complex covariance has conjugation on X), let P=E_{nu_a}[·|B] in the ordinary Euclidean L2(nu_a). Then P is a self-adjoint idempotent, and
  E[conj(X)*Y] =
    E[conj(PX)*PY] + E[conj((I-P)X)*(I-P)Y].

For centered X=Theta F_gamma and Y=translate_(n tau_a) F_gamma this is exactly
  M_(a,gamma)(n) = C_IR(a,gamma,n) + R_UV(a,gamma,n)
with
  C_IR=Cov_(nu_a,B)(E[X|B],E[Y|B]),
  R_UV=E_B Cov_(nu_a(·|B))(X,Y).
The identity is an exact law of total covariance for the same physical
Wilson marginal, not a heuristic decomposition.

**Strict Lean kernel certificate**:
YMOriginal/OriginalI7_ExactCoarseFineInner.lean,
YMUIC.I7RG.exact_coarse_fine_inner,
CI https://github.com/penghongzhong/YM-closed/actions/runs/43551652163
SUCCESS, only [propext, Classical.choice, Quot.sound].

The Lean theorem is about an arbitrary self-adjoint idempotent operator. Its concrete realization as Wilson conditional expectation and the blocking kernel's physical identity have NOT been kernel-certified. No theorem equates the true R_UV term with the old/new-R Mayer series.

**Decisive no-go:** even R_UV=0 for all n (e.g. F entirely coarse/B-measurable) does not imply exponential clustering of C_IR. The coarse sector alone can carry a gapless spectrum. Therefore Original24's ultraviolet R-control cannot by itself prove I7.

## B. New strictly weaker continuum-only sufficient condition

The original B14 theorem assumes exact per-cutoff contraction
  Qt(k,s,c) <= q Q0(k,s,c), q=exp(-td)<1
for all regulators k and all finite source families (s,c).

For the actual continuum Clay mass-gap goal, it is sufficient to prove
  (AS59)  Qt(k,s,c) <= exp(-td) Q0(k,s,c) + err(k)*cost(s,c)
for all k,s,c, where err(k)->0 on the SAME joint cutoff-volume limit filter, cost(s,c) is a finite real function independent of k, and
  Q0(k,s,c)->||sum_j c_j v_j||^2,
  Qt(k,s,c)->Re< Tcont(sum_j c_j v_j), sum_j c_j v_j>.
No relative condition number on Q0 and no finite-regulator exact I7 are required.

Fix s,c first and take the same filter limit:
 Re< Tcont x,x> <= exp(-td) ||x||^2.
Density and boundedness extend to all x. Under the explicit *continuum*
NonnegativeHeatCalculus Acont t Tcont (standard spectral-calculus interface),
  generatorGap(Acont) >= d > 0.

The proposition is mathematically valid on paper and avoids regulator-by-regulator I7. It requires a NEW continuum-only final statement: the historical
Original42UICMain explicitly asserts a common gap for every cutoff generator
AS WELL AS for the continuum generator. One cannot silently claim the old
statement from AS59; retain original count 39/39 CONDITIONAL.

New Lean source:
 YMOriginal/Original42_B14VanishingDefect.lean
 theorem b14_continuum_gap_from_vanishing_cutoff_defect.
Audit: official-pin CI must succeed before counting; raw hcut is a visible
true-model asymptotic estimate, not proved by this assembly.

### Exact remaining model bottleneck

Produce ONE uniform strict q<1 for the **complete terminal physical infrared
Wilson/OS Gram form**, plus a cutoff-vanishing absolute defect on each fixed finite source family. Original24 may help bound the ultraviolet defect only
once the exact source-jet/conditional-measure identity has been derived.
Its old/new-R smallness alone supplies NO bound q<1 for the full coarse
infrared covariance.

This asymptotic condition is logically weaker than the original I7 but, by
density and spectral calculus, is equivalent to the desired CONTINUUM gap;
it does not abolish the hard nonperturbative dynamical estimate.

## C. Strong-coupling and new 2026 literature

Shen–Zhu–Zhu, CMP 400 (2023), DOI 10.1007/s00220-022-04609-1:
published mass-gap and exponential correlation estimates at strong coupling,
without the required weak-bare-coupling continuum bridge.

Bhattacharjee et al., Hexagon 2610.00341 v7 (2026):
one-cube physical mixing is a sufficient condition but its full
continuum-tuning estimate remains OPEN.

Mir Faizal & Arshid Shabir, Fortschritte der Physik 74 (2026), e70097,
DOI 10.1002/prop.70097, claim a continuum SU(N) mass gap and weak-coupling
entry. Their journal abstract is publicly visible, but the precise
UV-to-IR scale-uniform estimate and identification with OUR actual
Wilson/OS model have not been independently checked in this project.
Do NOT promote abstract-level assertions into a paper theorem or a
Lean-certified external hypothesis. Clay Mathematics Institute continues
to list Yang–Mills existence and mass gap as UNSOLVED.

## D. Critical proof accounting

- Original A–F conditional modules: historical 39/39, not unconditional.
- True physical I7: OPEN.
- Exact RG marginal/conditional expectation dictionary: paper identity,
  model instantiation OPEN.
- True physical AS59 cutoff-vanishing full Gram estimate with strict q<1: OPEN.
- The new abstract B14 theorem (if strict CI passes) verifies the
  asymptotic-limit implication ONLY; never counts as solving physical I7.
- No published theorem is silently changed or weakened. Original42UICMain
  remains intact; continuum-only alternative target will have distinct name.
