# 第64轮｜I7原主定理纸面攻关：正性消去交叉项，钉住真实动力学红点

Date: 2026-11-14
Branch: ym-i7-round64-paper-only-20261114
Base: ym-i7-sourcewise-rare-20261114
STATUS: genuine physical 4D SU(2) I7 is **OPEN**. Original historical 39/39 only CONDITIONAL.
**User instruction honored:** because I7 paper proof is not closed, add NO new Lean theorem, run NO new Lean CI, and do not modify the accepted conditional main branch.

## 1. Actual finite-cutoff source: induced action's force-covariance Hessian

Let \mu_a be the exact 4D SU(2) Wilson Gibbs measure and c the
chosen finite-scale gauge-compatible block map. Represent the
push-forward coarse density by exact fibre integration:
  H^c(V)=-log Z_c(V),
  Z_c(V)= \int_{fine} exp[-S(V,m)] d\lambda(m).
The normalized same-model conditioned fibre law is
  d\zeta_V(m)=Z_c(V)^(-1) exp[-S(V,m)]d\lambda(m).

For derivatives D_e^X,D_j^Y in independent marked coarse link
directions, compactness and smoothness justify differentiation:
  D_e H^c=E_{\zeta_V}[D_e S].
Applying the quotient rule once more gives the EXACT finite-model identity
  D_j^Y D_e^X H^c(V)
    = E_{\zeta_V}[D_j^Y D_e^X S]
      -Cov_{\zeta_V}(D_e^X S,D_j^Y S).           (64.1)
For two marked raw links in no common plaquette, the mixed raw
Wilson-action derivative vanishes:
  D_j^Y D_e^X H^c(V)
    =-Cov_{\zeta_V}(D_e^X S,D_j^Y S).           (64.2)

These formulas are also established by Bhattacharjee et al.,
*One Cube Estimate Implies the Yang–Mills Mass Gap*, v7, Proposition
144; we do NOT claim priority. The authors explicitly identify
uniform-in-background and uniform-in-torus covariance summability
as unproved along the continuum tuning.

**Critical identification:** \zeta_V is the FULL true fibre measure
with its terminal IR effects, not the old/new-R remainder amplitude
and not the unconditional Wilson measure. The existing Lean
Original24_BalabanTwoRootRealFullSeries.lean does NOT prove the
full conditioned force covariance in (64.2). It only controls named
old/new-R connected-root sums under explicit count/FP/model inputs.

For the strong Dobrushin/Bakry–Émery route, a real criterion would
need a uniform strict margin in the complete coarse conditional
Hessian, involving both diagonal curvature AND the sum over all
off-diagonal conditional force covariances:
  sup_{regulator,volume,V,e}\sum_{j\ne e}\sup_{\|X\|=\|Y\|=1}
    |Cov_{\zeta_V}(D_e^X S,D_j^Y S)| < threshold,
with exact treatment of the nearby direct-plaquette terms.
This remains a MODEL RED, and it is a STRONGER sufficient route
than the original I7; no conditional covariance estimate of this
strength has been verified for weak-coupling SU(2) Wilson theory.

## 2. NEW paper lemma: positivity removes a separate cross-operator estimate

Let \mathcal H_\perp be a genuine physical OS vacuum-orthogonal
Hilbert space, T:\mathcal H_\perp\to\mathcal H_\perp positive
self-adjoint with 0<=T<=I, and P an **actual OS orthogonal
projection** (NOT Euclidean conditional expectation).
Set Q=I-P. Assume nonnegative constants q_c,q_f with
  <x,Tx> <= q_c ||x||^2  for every x in ran P,
  <y,Ty> <= q_f ||y||^2  for every y in ran Q.

For v=x+y with x=Pv, y=Qv, the positive operator
Cauchy--Schwarz inequality gives
  |<x,Ty>| <= sqrt(<x,Tx><y,Ty>)
             <= sqrt(q_c*q_f)||x||||y||.
Consequently,
  <v,Tv>
    <= q_c||x||^2+2sqrt(q_c*q_f)||x||||y||
                +q_f||y||^2
    =(sqrt(q_c)||x||+sqrt(q_f)||y||)^2
    <=(q_c+q_f)(||x||^2+||y||^2)
    =(q_c+q_f)||v||^2.

Since T>=0,
  ||T|| <= q_c+q_f.                              (64.4)
If the same q_c,q_f satisfy q_c+q_f<1 uniformly across all
actual regulators, volumes and all relevant nonvacuum sectors,
then the complete ORIGINAL I7 finite complex Gram inequality holds
with
  q=q_c+q_f<1, eta_*=1-q>0,
  G_0^{(M)}-G_*^{(M)} >= eta_* G_0^{(M)}
for EVERY finite coefficient family M.

Original B08 physical clock 2a_*<=2c_+/Lambda_YM then yields
  gap(H) >= [-log(q)/(2c_+)]Lambda_YM,
conditional on the previously recorded published OS/heat spectral
calculus and the SAME model transfer dictionary.

**Important improvement vs Round60:** no INDEPENDENT assumption on
\|PTQ\| is required. Positivity already yields
  \|PTQ\| <= sqrt(q_c*q_f).
In the earlier sufficient Schur condition
  \epsilon^2<(1-q_c)(1-q_f),
this automatic estimate suffices whenever
  q_c+q_f<1.
Thus the physically necessary quantitative tasks may be compressed
to TWO diagonal transfer compression bounds, not three.

**Sharpness without other assumptions:** on C^2, for q_c,q_f>=0
with q_c+q_f<=1, let
  T=[[q_c,sqrt(q_c q_f)],[sqrt(q_c q_f),q_f]],
  P=diag(1,0).
T is positive with eigenvalues 0 and q_c+q_f, and the bound
(64.4) is attained. At q_c=q_f=1/2 each compression is <1
but T has eigenvalue 1, so two individually strict estimates
with q_c+q_f=1 are NOT enough for I7.

**Physical REDs remain**:
A. construct P on the actual OS Hilbert space, compatible with
coarse Wilson sources and preserving vacuum-orthogonality;
B. prove a regulator/volume-uniform q_c<1 for the entire
nonperturbative terminal IR sector;
C. prove q_f<1-q_c for the TRUE fine compression of the
physical transfer T; UV old/new-R coefficient smallness alone
is not a compressed-T bound.

Do NOT derive q_f from a bare mean energy bound
  <y,Hy> >= E||y||^2
when Q is not invariant under H; e^{-tE} is convex in E,
and the spectral average can retain a low-energy tail.
Example: on a 2D nonvacuum subspace H=diag(delta,M) with
0<delta<<M and y=(e_delta+e_M)/sqrt2,
  <y,Hy>=(delta+M)/2 -> infinity,
  <y,e^{-tH}y>=(e^{-t delta}+e^{-t M})/2
      -> e^{-t delta}/2>0.
The desired q_f must be a genuine compressed transfer estimate,
or have an independently justified spectral/commutator argument.

## 3. The continuum-only variant can avoid proving a UNIFORM fine compression

This section is a distinct ALTERNATIVE, not closure of original I7.

For each k, take the actual nonvacuum OS projection P_k and test
v_{k,F} for a FIXED physical finite positive-time Wilson source F.
Put x=P_kv, y=(I-P_k)v, delta_{k,F}=||y||.
If the coarse compression has common q_c<1,
and \sup_k||v_{k,F}||<=M_F for that fixed F, positivity
and \|T_k\|<=1 yield
  <v,T_k v>
   <=(sqrt(q_c)||x||+||y||)^2
   <=q_c||v||^2+
          2sqrt(q_c)M_F delta_{k,F}+delta_{k,F}^2.

Thus if delta_{k,F}->0 on the SAME joint cutoff/volume net
for every fixed F, the original Round63 strictly compiled
b14_continuum_gap_from_sourcewise_error applies with
  err(k,F)=2sqrt(q_c)M_F delta_{k,F}+delta_{k,F}^2 ->0.
NO uniform bound on T_k over ALL of ran(I-P_k) is needed.

But neither the genuine OS P_k, nor delta_{k,F}->0
for all nontrivial RENORMALIZED local sources, nor q_c<1
is proved. This variant proves only a sourcewise
continuum-only criterion, not finite-k original I7.
Furthermore a coarse grid with fixed terminal physical spacing
a_*~Lambda_YM^{-1} is not automatically dense in the entire
continuum local Schwinger algebra. The physical source/OS
representation and density remain explicit dictionary obligations.

## 4. EXACT finite SU2 Wilson toron geometry: local flatness does not control global holonomies

On a periodic N^3 spatial torus (with any time extent), choose
sigma_3=diag(1,-1), theta_i in [0,2pi) and set
  U_{x,i}=diag(exp(i theta_i/N),exp(-i theta_i/N))
  for spatial directions i=1,2,3,
  U_{x,0}=I.
All spatial links commute and are independent of x; therefore
EVERY elementary plaquette U_p=I exactly, so
  S_W[U]=sum_p beta_W(1-Re tr(U_p)/2)=0.

But a spatial noncontractible winding loop along direction i has
  P_i=U_{x,i}^N
     =diag(exp(i theta_i),exp(-i theta_i)),
  (1/2)tr(P_i)=cos(theta_i).

Since the trace of a winding loop is invariant under periodic
gauge transformations, configurations with different cos(theta_i)
are not all gauge equivalent.

For theta_i=pi and N->infty,
  ||U_{x,i}-I||=2 sin(pi/(2N))->0,
  EVERY U_p=I,
  but (1/2)tr(P_i)=-1.
Hence a uniform local plaquette small-field condition,
and even arbitrarily small individual link deviations, does
NOT constrain global toron / winding sectors.

This is a strict finite-lattice SU2 algebraic construction, NOT an
upper bound on the quantum transfer gap and NOT proof of masslessness.
It shows that bare Wilson action convexity around flat links and
local rare-field estimates cannot alone cover all nonlocal sectors
of the original finite-torus I7. The continuum local OS version
may separate these global sectors but has to prove the correct
physical reconstructed Hilbert space and nontrivial local fields.

## 5. EXACT positive Haar-stationary transfer counterexample to the tempting shortcut

Let Haar h on SU2 and \Pi f=\int f\,dh be the orthogonal
projection onto constants. For 0<eps<1 define
  T_eps=(1-eps)I+eps \Pi.

It is a positive selfadjoint Markov contraction. Haar h is
EXACTLY stationary; all fixed nontrivial character expectations
under h vanish. On the centered spin-half character
  F(U)=tr(U),  ||F||_{L2(h)}^2=1,
  <F,T_eps^n F>=(1-eps)^n.
The nonvacuum transfer spectrum is the single value 1-eps,
so the gap per step tau equals
  m_eps=-log(1-eps)/tau->0 as eps->0.

Tensor independent copies spatially. The equal-time
spatial state is EXACT Haar product at every cutoff, with
vanishing connected correlations at distinct spatial sites,
while the positive reversible time-transfer may have
arbitrarily small gap. Such a stationary Markov path measure
has the expected 1D-time transfer RP. It is NOT the true 4D
Wilson plaquette action and NOT O(4)-invariant. It proves only
that Haarization/equal-time spatial mixing/transfer positivity
by themselves do not imply any time-gap estimate.

The 2026 Bhattacharjee et al. v7 result includes stronger
coarsest-scale conditioning statements on certain growing
finite tori; this toy does NOT refute their one-cube theorem
or its properly quantified BP hypothesis. It precludes
replacing those *conditional joint* estimates with marginal
Haar statements.

## 6. EXACT logical audit: Round63 sourcewise-B14 is equivalent to continuum Gram contraction

Assume for each fixed finite physical source F and fixed q<1
the SAME joint-limit net has scalar limits
  Q0_k(F)->Q0_cont(F), Qt_k(F)->Qt_cont(F).
Put D_k(F)=Qt_k(F)-q Q0_k(F).

Then these assertions are equivalent:
(a) D_cont(F)=Qt_cont(F)-q Q0_cont(F)<=0;
(b) there exists a source-dependent scalar eps_k(F)->0 such that
    D_k(F)<=eps_k(F) eventually.

Indeed (b)->(a) by taking the joint limit.
For (a)->(b) choose the explicit nonnegative error
  eps_k(F)=max(D_k(F),0).
Continuity of max and D_k(F)->D_cont(F)<=0
gives eps_k(F)->0, and D_k(F)<=eps_k(F) by construction.

Thus the useful Round63 Lean theorem formalizes a more
flexible ARGUMENT INTERFACE; mathematically it does not
independently produce q<1. The real analytic burden is
exactly the continuum physical gap or an explicit
model-generated producer of a strict, source-independent q.
Do not loop again through alternative error quantifiers in
place of proving physical infrared dynamics.

## 7. Paper-only final closure tree

4D SU2 original I7
|-- GREEN original 39/39 conditional main theorem ledger unchanged
|-- GREEN actual finite Wilson effective-action Hessian identity
|-- GREEN positive-OS two-compression bound:
|          q_total <= q_c+q_f, no separate off-diagonal norm
|-- GREEN exactly sharp 2x2 model, q_c+q_f<1 needed for this method
|-- GREEN SU2 flat toron algebra: U_p=I yet winding tr P_i=2cos(theta_i)
|-- GREEN Haar-stationary sticky transfer: equal-time Haar not mass gap
|-- GREEN sourcewise-B14 equivalence audit, no new dynamical strength
|-- YELLOW OS-vacuum-compatible coarse projection and actual source dictionary
|-- RED actual terminal q_c<1 uniform over regulator/volume/sector
|-- RED true transfer q_f<1-q_c uniformly on the complementary sector
|-- therefore I7 and the unrestricted mass-gap claim OPEN
|-- NO NEW Lean attempted because physical paper proof is not complete.

## 8. Next single physical proof target

Produce, in the SAME physical SU2 Wilson/OS model and
at the original fixed terminal time tau_k=2a_*(k):

1. A genuine dense enough gauge-invariant coarse OS subspace P_k,
   with the correct vacuum sector and source-to-block map;
2. \sup_k ||P_k T_k P_k|| <= q_c <1,
   with volume uniformity and all nonlocal/toron sectors relevant to
   ORIGINAL I7;
3. \sup_k ||(I-P_k)T_k(I-P_k)|| <= q_f <1-q_c.

It is NOT enough to use Bałaban old/new-R activities,
to show fixed-source sparse temporal correlations with
source-dependent rates, to bound a mean generator Rayleigh
quotient on a non-invariant fine subspace, or to show Haar
marginals at the terminal scale.

If 1--3 are independently proved on paper and all published
OS/heat inputs match the same Wilson model, the one-line
positivity bound (64.4) closes I7 and ONLY THEN should its
final Lean implementation/audit begin.

**External source:** Bhattacharjee et al., "One Cube Estimate Implies
the Yang--Mills Mass Gap," v7 (November 2026 text),
https://hexagonmath.org/2610.00341v7,
Proposition 144, Remark 145, Section X N-P;
explicitly says full continuum-tuned coarsest BP and
force covariance estimates remain unproved.
Clay Math Institute official problem page still says Unsolved:
https://www.claymath.org/millennium/yang-mills-the-maths-gap/.
