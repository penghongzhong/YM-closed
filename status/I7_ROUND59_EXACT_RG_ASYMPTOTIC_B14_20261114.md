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

## E. Strict latest main-chain verification and exact final-status clarification

**Strict latest CI**: https://github.com/penghongzhong/YM-closed/actions/runs/43552243134
SUCCESS, pinned Lean 4.35.0-rc3 / Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee;
only [propext, Classical.choice, Quot.sound], no sorry/admit/new axioms.

1. YMOriginal/Original42_B14VanishingDefect.lean:
   b14_continuum_gap_from_vanishing_cutoff_defect.
   Its upgraded model condition is per-source **EVENTUAL**:
     for all fixed finite s,c, eventually k in the same limit filter:
       Qt(k,s,c) <= exp(-td) Q0(k,s,c) + err(k) cost(s,c).
   The cutoff threshold may depend on s,c. err(k)->0 in the SAME filter.
   No relative finite-cutoff I7 and no regulator-level uniform gap assumed.
2. YMOriginal/Original42_ContinuumOnlyAsymptotic.lean:
   Original42ContinuumOnlyMain,
   original42_continuum_only_from_asymptotic_gram.
   All original phase/OS/nontriviality stages survive, and the
   continuum generator gap is **derived**, not passed as theorem input.
   The old Original42UICMain remains unchanged (and still requires
   per-regulator uniform gap, I7).

This is an alternative conditional theorem with a different, explicitly
weaker conclusion (only continuum gap), not acceptance of historical
I7 or a silent alteration of the 39-environment inventory.

## F. Precise critical physical dictionaries still OPEN

1. **Same-theory OS/Hilbert pairing.** The typed PublishedOSII
   structure only records an abstract WightmanTheory and a predicate
   euclideanBoundaryOf W Hsch. It does NOT assign the actual reconstructed
   Wightman Hamiltonian and physical Hilbert space to the independent
   Acont/Tcont/v variables of the B14 proof. A genuine SU(2) Wilson
   GNS/OS realization theorem must establish that these variables describe
   the SAME Hsch produced by the actual Wilson state. An unrelated gapped
   Hilbert space may satisfy the abstract B14 theorem but is not a mass
   gap for the Yang--Mills Wightman theory.
2. **Fixed physical time.** B08 only bounds the terminal time
     2 a_*(k) in [2 c_-/Lambda_YM, 2 c_+/Lambda_YM].
   It does NOT automatically assert that a_*(k) converges to a particular
   fixed t/2. A valid source dictionary should either show
   cofinal convergence or choose a universal later physical time
   t>=sup_k 2a_*(k), with a positive spectral semigroup and compatible
   microscopic time rounding, then prove the same-net Qt limit at that t.
3. **True terminal R-budget.** U1 gives 0<g_j<=gamma and old/new-R
   prefactors controlled by g_j^kappa0 and exp(-p0(g_j)); it does
   NOT imply g_(K(k))->0 at the stopping scale. Hence terminal R-error
   need not vanish with cutoff. To use B14, absorb any persistent terminal
   error *relatively* with a quantified contraction budget
     qIR + deltaTerminal <1,
   and leave only a genuinely cutoff-vanishing absolute error
     epsUV(k) cost(s,c), epsUV(k)->0.
   Neither strict qIR nor the relative deltaTerminal bound has been
   established for the full nonperturbative Wilson coarse action.
4. **Source renormalization.** cost(s,c) must remain cutoff independent
   for each fixed physical renormalized Wilson-source family. Bare
   coefficient norms may diverge with lattice normalization; Original30's
   fixed-K polynomial-budget interface is not automatically a proof
   of such uniformity at the fully renormalized level.

This is why the alternative formal proof is conditional and why
published UV polymer smallness does not by itself close the dynamics.

## G. Exact final countermodel to the UV-only shortcut

Choose any nontrivial factorized probability theory with coarse
variables B and fine variables Z independent, and let the Wilson-test
analogue F depend only on B. Then P=E[·|B] satisfies (I-P)F=0, so the
fine/UV conditional covariance vanishes IDENTICALLY, at every time.
The coarse sector may nevertheless have a positive selfadjoint transfer
with eigenvalues exp(-1/j), j>=1, accumulating at 1, and hence no
uniform gap. This is a logical nonimplication, not an SU(2) YM model.

Therefore even perfect control of the ultraviolet residual cannot
replace an independent estimate of nonperturbative coarse infrared
mixing. This remains the unique dynamical RED of the bypass route.

## H. Final closure tree ledger

Existing conditional 39/39 PASS preserved.
Round55-58 new strict algebra/scalar certificates: 12 PASS.
Round59 exact coarse/fine Hilbert identity: 1 PASS (CI 43551652163).
Round59 B14 vanishing-defect proof: 1 PASS (CI 43552243134).
Round59 distinct continuum-only conditional bookend: 1 PASS (same CI).
Original physical I7: OPEN.
Actual physical Wilson asymptotic Gram inequality with common q<1: OPEN.
OS same-model physical Hamiltonian realization: OPEN.
Unconditional SU2 Yang--Mills mass gap: OPEN.

Do not combine these new auxiliary theorem counts into the historical
39-environment denominator. No claim that the actual Clay existence
and mass-gap problem has been solved.

## I. Limit-order improvement: fixed physical t, no finite-k all-time bootstrap

The Round58 finite-regulator route required infinitely many dyadic time
moments at EACH cutoff, and any nondecaying error floor obstructed
n->infinity.

The Round59 continuum route instead fixes ONE physical time t>0 and
a finite family s,c, and sends the joint regulator-volume index k along
the SAME filter. A source error err(k) cost(s,c) is harmless as soon as
err(k)->0, even if it does not decay with time at fixed k.

This is a genuine logical weakening, not a new dynamical estimate.
A simple strictness example: H_k=C^2 with
T_k=diag(q,1-1/k), 0<q<1, and physical test vector e1 only.
The full regulator generator has gap approaching zero because of e2,
so no uniform regulator I7 holds. But the continuum test family e1
has Tcont=qI on Hcont=C and the exact Gram limit is gapped. This toy
example is NOT Yang–Mills; it shows that the continuum physical target
need not require every regulator-level excitation to stay gapped.

## J. More physical source-matched variant

New source YMOriginal/Original42_SameHierarchyAsymptotic.lean:
  original42_continuum_only_from_same_schwinger_gram.

Unlike a purely abstract bookend, this variant forces both finite-cutoff
Gram forms Q0/Qt to be evaluations of the SAME cutoff Schwinger
hierarchies Hcut at positive-time polynomial test inputs p0 and pt,
and requires their limits to be the SAME Hsch entering
Original34ManuscriptInputs and PublishedOSII. The two exact matching
identities hMatch0/hMatcht identify these continuum Euclidean
pairings with the Hilbert norm and continuum physical-time transfer
pairings. Their source dictionary and the same-net Schwinger
convergence are genuine physical/model inputs, not yet derived from
the actual Wilson measure.

This eliminates the *formal possibility of attaching a wholly unrelated
gapped Hilbert model to the U-I-C Schwinger hierarchy*, but does
not by itself prove that all physically relevant positive-time
test polynomials are exhausted or that Hcont is the physical
reconstructed Hamiltonian for Yang–Mills. Full OS/GNS realization
and source exhaustiveness remain model obligations.

New exact same-hierarchy Lean CI:
https://github.com/penghongzhong/YM-closed/actions/runs/43552682497
**SUCCESS**: `original42_continuum_only_from_same_schwinger_gram` compiled under pinned Lean 4.35.0-rc3 / Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee with only `[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/new axioms. It is a model-input-conditional theorem, NOT a proved physical RG estimate.

## K. Final single physical RED

For a chosen fixed physical time t and every finite physical
renormalized Wilson test family s,c, prove in the actual same
cutoff-volume lattice source net:

  eventually k:
    Qt(k,s,c) <= q Q0(k,s,c) + err(k) cost(s,c),
  q<1, err(k)->0, cost(s,c)<infty cutoff independent.

Quantitative RG synthesis may take the form

  q=qIR+deltaTerminal<1,
  err(k)=epsUV(k)->0.

The strict qIR and terminal relative error margin for the COMPLETE
interacting infrared measure remain OPEN. The existing U1
g_j<=gamma bound does not imply the terminal R contribution vanishes.

Time registration must ensure Qt(k,s,c) at a single fixed positive
physical t converges to the physical OS Tcont(t), despite B08 terminal
times 2a_*(k) varying in a compact positive interval. Positivity of
exp(-tH) may allow comparison at a common later time, but the same
source and limit dictionary has to be proved, not assumed.

The original historic 39/39 conditional inventory remains unchanged.
Physical I7 and unconditional Yang–Mills mass gap remain OPEN.

## L. Stronger reuse of the original old/recent two-limit technique, without pretending to prove IR contraction

The repository's already-accepted
`YMConditional/Original25_TwoScaleLimit.lean` proves
`fixed_cut_limit_bound` and `equal_limits_of_old_recent`:
for any fixed history cut N, a geometric old-history tail remains
while the recent error vanishes along the SAME cutoff-volume net;
only AFTER removing this cutoff does one send N->infinity.
Its application there is rotation matching, NOT I7.

The analogous, potentially weaker *actual model* hypothesis for the
new continuum-only B14 is the following. Fix a single physical
time t>0, q in (0,1), and each finite physical renormalized source
family (s,c). Write the actual full physical Gram excess:
  D_k(s,c) := Qt(k,s,c) - q Q0(k,s,c).

**Two-limit model target T59**: there exist
  0<=rho<1, A(s,c)<infinity, and
  for each N in Nat a finite C_N(s,c),
together with a cutoff-scale parameter xi(k)->0, such that
for every *fixed* N,s,c,
  eventually k in the SAME joint regulator-volume filter:
    D_k(s,c) <= A(s,c)*rho^N + C_N(s,c)*xi(k).
The constant C_N may depend arbitrarily on N,s,c, and no
factorization `err(k)*cost(s,c)` for all k is assumed.

**Exact paper deduction**: same-net Gram convergence gives
  D_k(s,c) -> D_cont(s,c)
  = Re< Tcont x,x> - q||x||^2.
Fix N and take the joint cutoff/volume limit:
  D_cont(s,c) <= A(s,c)*rho^N.
Then take N->infinity to obtain D_cont(s,c)<=0. By density,
  Tcont<=qI and generatorGap(Acont)>=-log(q)/t,
provided the same physical OS Hilbert/Schwinger pairing and positive
heat spectral calculus are established.

This is more flexible than the first uniform additive-defect interface,
and recycles the exact N-first / cutoff-second proof bookkeeping
already Lean-checked in Original25. T59 is a rigorous PAPER
implication, NOT an independently kernel-accepted new theorem.
In particular **the crucial strict q<1 has still not been proved** on
the full physical Wilson IR sector. Moreover, the Original25 old/recent
bounds for rotations are NOT automatically the required bounds for
the physical Gram excess; an exact model dictionary is still absent.

A source-uniform `A` is NOT necessary for this continuum-only
criterion, as the finite source (s,c) is held fixed before taking
either limit. However the common `q<1` must be fixed independently
of s,c. Non-uniform source-dependent q would not give an operator gap.

## M. Updated strict status (after same-hierarchy CI)

- Historical 39/39 **CONDITIONAL**, unchanged.
- Round55–58 prior auxiliary Lean certificates: 12 accepted.
- Round59 coarse/fine Hilbert projection identity: 1 strict PASS,
  CI 43551652163.
- Round59 asymptotic B14, continuum-only bookend, source-matched
  same-Schwinger bookend: 3 strict PASS,
  last CI 43552682497.
- Physical I7: OPEN.
- True full-Wilson strict IR contraction q<1 (or T59): OPEN.
- Actual OS reconstruction identifying the exact same physical
  Hamiltonian and dense test space: OPEN model dictionary.
- No unconditional 4D Yang--Mills mass gap is established.
