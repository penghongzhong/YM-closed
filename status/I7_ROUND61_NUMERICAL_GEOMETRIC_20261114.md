# 第61轮｜I7 启发式、数值及几何主链审计

Date: 2026-11-14
Branch: ym-i7-numerical-geometric-20261114
Base: bc4a285d5ab69e6afd2db9d74dbb7a394e6e6e5f
**Acceptance: actual physical I7 OPEN. Original 39/39 CONDITIONAL unchanged. No new Lean theorem counted this round.**
All model toy formulas, Monte Carlo results and path-entropic proposals are deliberately classified as heuristic or conditional. No claim of four-dimensional continuum Yang--Mills mass gap.

## 1. Exact compact SU(2) convolution laboratory (not the Wilson physical transfer)

For U in SU2, let tr(U)/2=cos(theta) and Haar class density (2/pi) sin(theta)^2 dtheta. Normalize
  K_beta(U) = Z_beta^(-1) exp(beta * tr(U)/2).
Class convolution T_beta has Peter--Weyl eigenvalues
  lambda_j(beta) = I_(2j+1)(beta)/I_1(beta).
In the nonconstant sector, the largest eigenvalue is lambda_(1/2)=I_2(beta)/I_1(beta).
As beta tends to infinity,
  q_toy(beta)=1-3/(2 beta)+O(beta^(-2)).
Thus an **unblocked bare** weak-coupling q_toy tends to 1. The genuine 4D Wilson OS time-transfer is NOT this single-link convolution; using it as a physical q_IR would be invalid.

Numerical exact values:
beta 1: 0.240194, 2:0.433127, 4:0.658047, 8:0.819249,
16:0.907815, 24:0.938180, 32:0.953503, 50:0.970153.

For the abstract two-channel Schur upper bound
  q_eff=(q_c+q_f+sqrt((q_c-q_f)^2+4 eps^2))/2,
using illustrative q_c=q_toy(beta), q_f=0.60, eps=0.15,
the certificate q_eff<1 holds precisely when
  q_toy(beta)<1-eps^2/(1-q_f)=0.94375,
i.e. beta<26.404109... in this toy.
At beta=16 q_eff=0.96882; beta=24 q_eff=0.99512;
beta=32 the upper bound exceeds 1 and is VACUOUS, not
a violation of contraction by the actual physical transfer.

The model-side RED is not a numeric beta threshold: it is
the existence of a genuine cutoff/volume-uniform terminal coarse q_c<1,
a fine q_f<1 and an OS-compatible cross-norm eps with
  eps^2 < (1-q_c)(1-q_f).
All three inequalities require a true SU2 OS transfer, not bare
single-link group convolution or Euclidean-only conditioning.

## 2. A new physically relevant spectral warning: tiny overlap hides slow modes

For a positive selfadjoint contraction T and a vector v, the moments
  M_n=<v,T^n v>=integral_[0,1] lambda^n dmu_v(lambda)
satisfy the Cauchy--Schwarz log-convexity
  M_(n+1)^2 <= M_n M_(n+2).
Hence, when M_n>0, ratios r_n=M_(n+1)/M_n are
NONDECREASING and converge to the essential upper spectral endpoint
visible to v. The effective masses -log(r_n)/tau are NONINCREASING.
A finite-time estimate r_n<1 never gives an upper bound on the
full transfer norm.

Explicit toy counterexample:
  M_n=(1-10^(-8))*0.25^n + 10^(-8)*0.999^n.
Ratios:
  r_0=0.25000, r_8=0.25049, r_10=0.25770,
  r_12=0.35651, r_14=0.79363,
  r_16=0.98169, r_20=0.99893 ->0.999.
An invisible slow-mode weight as small as 1e-8 controls the asymptotic
spectral edge. This is a precise reason numerical short-time
Wilson estimates cannot certify I7.

## 3. True small FOUR-DIMENSIONAL SU(2) lattice MC, NOT continuum proof

Used actual 4D hypercubic periodic Wilson action
  S_W=-beta sum_p (tr U_p)/2,
SU2 links as unit quaternions, symmetric local left-rotation
Metropolis proposals, and spatial plaquette mean averaged over
the three spatial orientations on each Euclidean-time slice.
Time size Lt=8. Spatial sizes Ls=3,4.
A linked external update changes exactly the six incident
plaquettes; random-link tests confirmed delta(local action)
=delta(global full action) within numerical precision.
A full random SU2 sitewise gauge transform on Ls=3,Lt=8
gave maximal gauge-invariance error 9.99e-16 over 1296 plaquettes.

For Ls=3, after 1200--2300 burn-in sweeps, 3200 measurements
each separated by four full Metropolis sweeps:
beta | <tr U_p/2> | C1/C0 | approximate 95% block-bootstrap CI
1.0    0.24237        0.00216       [-0.0118,0.0168]
2.3    0.61410        0.10425       [0.0860,0.1215]
2.6    0.67427        0.05261       [0.0359,0.0691]
2.9    0.71508        0.04994       [0.0353,0.0637]

At beta=2.3 with Ls=4, after 1400 sweeps and 2600 measurements
separated by four sweeps,
  <tr U_p/2>=0.60842,
  C1/C0=0.09520, bootstrap CI [0.0753,0.1134].
The two sizes' C1/C0 intervals overlap; this does not establish
volume-uniform mass.
For beta=2.3,
  Ls^3 C0(Ls=3) = 27*0.00186036 = 0.0502297,
  Ls^3 C0(Ls=4) = 64*0.000780506 = 0.0499524.
This is suggestive of short-distance spatial fluctuation averaging,
not a proof of exponential time clustering.

Important: finite periodic time includes backward wrapping, the
plaquette has no guaranteed overlap with every excited sector,
and volume Ls=3/4 is far from any thermodynamic/continuum limit.
Sampling uncertainties have not been corrected for all possible
topological trapping or continuum-renormalization effects.

## 4. Two-operator Wilson variational experiment is more relevant

Measured both the spatial plaquette mean F1 and oriented 2x1 spatial
rectangular Wilson loops F2 at beta=2.3, on Ls=3 and Ls=4,
Lt=8. Use zero-mean same-time covariance G0 and one-time shift G1,
symmetrizing the empirically estimated G1. Generalized eigenvalues of
  G1 c=lambda G0 c
obey the finite-subspace variational inequality
  lambda_max(G1,G0)<=||T||,
NOT the opposite inequality.

Ls^3  plaquette Rayleigh   rectangle Rayleigh   max 2x2 eigen
3       0.10481              0.12845             0.12846
4       0.11806              0.14872             0.14886

Block bootstrap (95%) for max 2x2:
  Ls3: [0.1084,0.1489], Ls4: [0.1278,0.1696].
The larger Wilson source family captures a SLOWER visible mode.
This supports using matrix-valued source Gram tests to **falsify**
overoptimistic conjectured margins. It cannot certify an operator
spectral upper bound, which requires a rigorous analytic bound over
the whole physical Hilbert space.

## 5. Path geometry: explicit 4D entropy-vs-energy threshold

For simple nonbacktracking nearest-neighbor paths in Z^4,
the first step has <=8 choices and each additional step <=7:
  N_ell <= 8*7^(ell-1).

IF (unproved for true YM) the complete connected Wilson/OS
two-root covariance, including ALL infrared sectors and branched
polymer decorations, admits an actual nonnegative dressed-path majorant
with a cutoff/volume-uniform per-block weight w, then for root
separation at least n physical blocks:
  |Cov(F,G)| <= A_(F,G) sum_(ell>=n) N_ell w^ell
             <= (8/7)*A_(F,G)*(7w)^n/(1-7w).
A positive physical decay exponent follows if 7w<1:
  m_geom=(1/a_*)log(1/(7w))>0.

This is a **conditional geometric criterion**, NOT a bound
for true 4D SU2. The dressed w must already incorporate
off-path trees, large-field fluctuations and full nonperturbative
coarse action. A small old/new-R polymer activity alone does not
supply such a full-IR w. The count 7 is the nonbacktracking
walk connective overbound, not a bound for arbitrary 4D lattice animals.

Illustrations: w=0.08 -> 7w=0.56, m_geom*a*=0.5798;
w=0.12 ->7w=0.84, m*a*=0.1744;
w=0.14 ->7w=0.98, m*a*=0.0202.

## 6. CORRECTION: proper orientation of one-loop RG coupling

In SU2, b0=11/(24 pi^2)>0 and the perturbative flow from UV
toward IR, blocking by L>1, is

  g_k^(-2) ~= A0 - b*k,   b=2 b0 log L>0.

Earlier notes used g_j^2~1/(A+t*j) without specifying the
REVERSE indexing direction. That positive-denominator form describes
IR-to-UV orientation, not a direct UV-to-IR RG recursion.
At terminal A_K~A_*>0, g_K^2 stays of order one:
one cannot claim the terminal prefactors vanish.

For L=2, b=0.0643779517, stop at A_*~4:
 A0=20, K=248, sum g_k^4=3.10580;
 A0=80, K=1180, sum g_k^4=3.68737;
 A0=320,K=4908, sum g_k^4=3.83390.
The FULL marginal fourth-order sum remains O(1), not o(1).
The first-order sum of g_k^2 grows with the cutoff depth
and must be renormalized, not treated as an absolutely summable error.

**Critical useful decomposition:** fix an integer N of FINAL IR layers
and treat all older UV layers separately. Since
  A_(K-j)=A_K+b*j >= A_*+b*j,
then for K>=N:
  S_UV(N) = sum_(k=0)^(K-N) g_k^4
          <=sum_(j=N)^infinity 1/(A_*+b*j)^2
          <=1/(A_*+b*N)^2+1/[b*(A_*+b*N)].
The bound tends to ZERO as N->infinity uniformly in A0.
This is a rigorous estimate WITHIN the one-loop toy recursion,
not a true Wilson source-bound theorem.

For A0=320, terminal A_*~4, numerical UV tails:
N=0:3.83390; 50:2.10295; 100:1.43952;
250:0.72444;500:0.38068;1000:0.17863.

The complementary last N terminal RG layers contribute a positive
O(1) amount and MUST be controlled nonperturbatively. UV summability
does not by itself manufacture the IR gap, but this split establishes
how an actual old/recent TWO-LIMIT strategy could avoid uniform
smallness of the full weak-coupling budget.

## 7. The unique new physical target

Focus on the already strictly compiled Round59:
  b14_continuum_gap_from_vanishing_cutoff_defect,
  original42_continuum_only_from_same_schwinger_gram.
Their named same-Schwinger/hilbert source and physical Hamiltonian
dictionaries still need a REAL model realization.

For a fixed physical time t and a finite normalized Wilson source
family F, seek an exact same-measure RG decomposition
  Q_t^(a)(F) - q Q_0^(a)(F)
    <= A_F * r_N + C_(F,N)*xi_a,
where 0<q<1 is uniform over source, cutoff, volume and N,
  r_N <= 1/(A_*+bN)^2+1/[b*(A_*+bN)] ->0
is an illustrative upper rate derived only from one-loop coupling
bookkeeping, and xi_a->0 as the cutoff-volume net is removed.
Crucially the new analytical producer must connect the TRUE
Wilson source Hessian to the UV tail and provide a true nonperturbative
strict q for the FULL remaining IR terminal sector. It must also
control OS-positive time blocking and the same physical Schwinger
hierarchy.

Fix N first; send cutoff/volume to infinity; then send N to infinity.
If these actual model premises are proved, the existing strict
B14 same-net theorem yields continuum mass gap. They are NOT proved.

A weaker operator route at one fixed N0 is also sufficient if the
UV/IR comparison is a UNIFORM RELATIVE OPERATOR NORM perturbation
smaller than the strict reference spectral margin; absolute per-source
errors at one fixed N0 are NOT enough.

The numerical benchmarks and path geometry help select a feasible
parameter region but cannot establish a uniform analytic q.

## 8. Grounded published evidence, distinct from proof

- Lucini, Teper and Wenger's published SU2 lattice scalar glueball
  benchmark m_0++/sqrt(sigma) ~=3.78(7) is summarized in
  https://link.springer.com/article/10.1140/epjc/s10052-018-6101-9.
  This is empirical evidence only for one channel.
- Bałaban's published 4D small-field RG supports UV-scale
  renormalization, not a proved uniform complete continuum IR gap:
  CMP109 (1987), DOI 10.1007/BF01215223;
  CMP116 (1988), DOI 10.1007/BF01239022.
- The Clay Yang--Mills existence and mass gap problem remains open.
- No new Lean environments were added; the past historical 39/39
  CONDITIONAL count stays unchanged.

**Final Round61 result: physical I7 OPEN, but the UV tail and
nonperturbative terminal block are now sharply separated, with
numerically calibrated spectral/geometry bottlenecks.**
