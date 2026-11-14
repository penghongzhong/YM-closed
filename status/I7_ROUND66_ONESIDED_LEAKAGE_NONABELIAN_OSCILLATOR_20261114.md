# 第66轮｜I7 纸面攻关：H1/H2 严格边界、正时间信息泄露及非阿贝尔量子束缚

Date: 2026-11-14
Branch: ym-i7-round66-one-sided-leakage-20261114
Parent: ym-i7-round65-os-one-sided-20261114

## 状态与本轮执行标准

4D SU(2) physical original I7 = **OPEN**.
Historical 39/39 are **CONDITIONAL**, with I7 as an explicit physical premise.
No newly verified physical model mass gap. No new Lean declaration, no CI
and no claim of a complete Clay Yang--Mills solution, because PAPER closure
has not occurred. This continues the user's "paper first, Lean only after
full paper closure" policy.

The genuinely new paper results are the NESTED CONDITIONAL VARIANCE
identity and its entropy-controlled leakage estimate; a complete toy
0+1-dimensional SU2 commutator quantum-coercivity proof; and a sharp
source normalization diagnostic. None supplies the model IR q<1.

## A. Important correction to prior Round65 priority:
## fibre force-covariance FC yields H1, but NOT H2

Verified by reading the actual PDF text and the PDF screenshots pp.84--85
of "One Cube Estimate Implies the Yang--Mills Mass Gap" v7:
https://hexagonmath.org/pdf/2610.00341v7

- Proposition148 and Corollary149 use uniform conditional fibre
  force covariances K_(e,e') to prove the coarsest effective coarse-link
  mixing condition (H1).
- The article explicitly states (pp. 83--85, Remark155):
  in the 4D compact U(1) Coulomb phase, Gaussian analogue
  of FC/H1 can hold even though the photon is massless;
  hence H1 alone cannot imply the physical gap;
  H2 is the separate genuinely non-abelian dynamical step.
- The authors state that H1 itself is open along the complete
  continuum tuning, and H2 is likewise unproved.

Therefore the Round65 proposed target
  sup_j sum_(e!=j)K_(e,j)<2/pi²
is a legitimate stricter *H1* target, NOT a gap producer.
Any argument "force-covariance row sum => physical q_IR<1"
that omits H2 would imply the same false conclusion in a
massless U(1) Coulomb analogue and must be rejected.

## B. Exact one-sided/full-coarse conditional-variance Pythagoras

Take the actual finite SU2 Wilson Euclidean probability (or
any probability space), with sigma-algebras
  B_+ subset B_full = sigma(B_+,B_-).
For complex L2 random observable F define
  P_+F=E[F|B_+], P_full F=E[F|B_full].
Then P_+ P_full=P_+, and
  F-P_+F=(F-P_full F)+(P_full F-P_+F)
is an orthogonal decomposition in ordinary complex L2(mu).
Thus the exact identity is
  E Var(F|B_+)
    = E Var(F|B_full)
      + E|E[F|B_full]-E[F|B_+]|².      (66.1)

The second term, here L_F, is exactly the information-leakage
defect from the full two-sided block sigma-algebra to the
positive-time block algebra. A small full-fibre Poincare
constant bounds the FIRST term only. It cannot be inserted
into the OS positive-time projection inequality without
also bounding L_F.

The sigma-algebra inclusion is a real model obligation:
if global RG paths cross the reflection plane, defining
B_+ as a subset of B_full may require a new one-sided,
reflection-compatible blocking map, not merely a new notation.

### Explicit RP two-time sharp counterexample

Let X_+,X_- in {+1,-1} and
  P(X_-=t,X_+=s)=(1+r*s*t)/4, 0<=r<1.
Reflection swaps the two variables.
For any positive-time f(s)=a+b*s,
  E[conj(f(X_-))*f(X_+)]=|a|²+r|b|²>=0:
the law is reflection positive.
For centered F=X_+, its OS norm squared is r.

Let full coarse B=X_-+X_+, let B_+ be trivial.
Then
  E[F|B]=B/2,
  E Var(F|B)=(1-r)/2,
  Var(E[F|B])=(1+r)/2,
  E Var(F|B_+)=Var(F)=1.
As r->1, the complete fibre variance tends to zero
while one-sided fibre variance remains 1 and
  ||[F]||_OS²=r->1.
Therefore small full-conditioned variance does not even
imply small OS approximation error.

Table r | full-fibre var | leakage | one-sided var | OS norm²:
0.5    0.25     0.75     1    0.5
0.9    0.05     0.95     1    0.9
0.99   0.005    0.995    1    0.99
0.999  0.0005   0.9995   1    0.999.

## C. Quantitative conditional mutual-information sufficient input

For a fixed bounded real or complex Wilson random variable
|F|<=M and regular conditional laws, by dual total-variation
and Pinsker:
  |E[F|B_+,B_-]-E[F|B_+]|²
      <=2M² D_KL(Law(F|B_+,B_-) || Law(F|B_+))
in the respective conditional expectation sense.
Average to obtain
  L_F <=2M² I(F;B_-|B_+),               (66.2)
with conditional mutual information in NATURAL log units.

Consequently, if P_OS is the actual OS Hilbert orthogonal
projection on the closed span of positive-time coarse
cylinders, the Round65 exact contraction of the OS norm by
ordinary L² gives for each centered positive-time source
  delta_(k,F)²
    :=||(I-P_OS)[F]||²_OS
    <= E Var(F|B_+)
    <= E Var(F|B_full)+2M_F² I(F;B_-|B_+).

This is a valid **two-input model target**:
  (1) true full-fibre variance ->0,
  (2) one-sided conditional information leakage ->0.
For variable/unbounded renormalized F, TV/Pinsker must
be replaced by conditional Lp or entropy-energy estimates;
one cannot assume a uniform bare Wilson supbound.

Neither model estimate (1) nor (2) has been produced from
the full 4D SU2 Wilson measure. Bounding (2) may itself
require nonperturbative time mixing/H2, so the criterion
must NOT be presented as a solved estimate or shortcut.

If both vanish for fixed F, and the actual coarse OS
transfer has a cutoff/volume-uniform q_c<1, then
the already strictly verified Round63 sourcewise B14
proves the continuum-only gap under real same-hierarchy
OS/Schwinger matching and fixed physical time.
For ORIGINAL finite-cutoff I7, a further complement
q_f or Schur cross bound is required; the new criterion
does not establish it.

### Markov-screening caveat

For a local reflection-positive Markov random field,
conditioning on the ENTIRE microscopic reflection-plane
boundary can make positive/negative-time halves
conditionally independent, so the second leakage term
may vanish if that full boundary belongs to B_+.
But including the entire microscopic time-zero slice
may already generate the complete physical transfer
Hilbert space; coarse compression q_c then becomes
the original unproved physical norm ||T||<1.
Consequently this screening observation is not by
itself a non-circular mass-gap proof.

## D. A genuine, distinct SU2 non-abelian quantum mechanism
## exact 0+1 dimensional matrix-model proof; NOT a 4D result

Let x,y in R³ represent SU2 algebra directions and g>0. Define
  H_g=-Delta_x-Delta_y+g²|x cross y|²
as a Friedrichs Schrödinger operator on L²(R^6).

The classical magnetic commutator potential is zero for
collinear x,y; therefore no uniform pointwise quartic
lower bound is available along commuting valleys.

Nevertheless, for each fixed x,
  -Delta_y+g²|x cross y|² >=2g|x|    (D.1)
as quadratic forms. Indeed rotate x onto the third axis;
the y1,y2 operators are two independent 1D oscillators
  -d²/dy_i² +(g|x|)² y_i² >=g|x|,
with the y3 kinetic term nonnegative.
Similarly,
  -Delta_x+g²|x cross y|² >=2g|y|.

Average the two inequalities in the exact decomposition
  H_g=-(Delta_x+Delta_y)/2
      +[-Delta_x+g²|x cross y|²]/2
      +[-Delta_y+g²|x cross y|²]/2
to obtain
  H_g >=-0.5(Delta_x+Delta_y)+g(|x|+|y|). (D.2)

The lower comparison operator has compact resolvent
because the confining potential tends to infinity.
The lower quadratic-form bound plus the compact
embedding of the comparison form domain therefore
implies H_g has compact resolvent too.
Its heat semigroup is positivity improving on connected
R^6, hence the ground-state eigenvalue is simple;
the discrete spectrum yields a strictly positive
first excitation gap E_1(g)-E_0(g)>0.

Scale x,y by g^(-1/3) to see
  H_g unitarily equivalent to g^(2/3) H_1,
so the excitation gap scales as g^(2/3).

This elementary rigorous example belongs to the
bosonic Yang--Mills QUANTUM-MECHANICS family and
is related to Barry Simon, "Some quantum operators
with discrete spectrum but classically continuous
spectrum", Annals of Physics 146 (1983), 209--220,
DOI:10.1016/0003-4916(83)90057-X.
It is not claimed as an original physical result.

Potential non-Abelian route for the true terminal IR model:
use a gauge-invariant, reflection-compatible version
of quantum transverse oscillator/commutator coercivity,
not merely the CLASSICAL bare action Hessian;
control all commuting Cartan valleys, Gauss constraints,
noncontractible toron sectors, boundary interactions
and residual RG corrections, with constants uniform
in spatial volume and cutoff at the original terminal
physical clock 2a_*.

NONE of these 4D estimates has been proved.
The bare g->0 scaling g^(2/3) in the toy does not give
a cutoff-uniform physical mass without a rigorous RG
normalization and continuum transfer dictionary.

## E. Quantitative source renormalization diagnostic: raw Wilson
## boundedness alone can conceal a trivial continuum limit

Let U in SU2 have exact one-group class law
  nu_beta(dU)=Z_beta^(-1) exp(beta*tr U/2) dHaar(U),
where Z_beta=2 I_1(beta)/beta, and define
  W(U)=1-(1/2)tr U.
Then
  E cos(theta)=d/d beta log Z_beta
              =I_2(beta)/I_1(beta),
  Var(cos(theta))=d²/d beta² log Z_beta.

As beta->infty, beta W converges in distribution
to (1/2) chi²_3, hence
  E(beta W)->3/2,
  Var(beta W)->3/2.

Numerical exact Bessel high-precision checks
beta | E(beta W) | Var(beta W):
 10      1.458146916763   1.411186654687
 50      1.492345921219   1.484533536940
 100     1.496211999184   1.492385487913
 1000    1.499624624507   1.499248873027.

But ||W||_infty<=2 while ||beta W||_infty<=2beta
grows, despite a finite limiting variance for beta W.
Thus a cutoff-independent bad-field error budget for
BARE Wilson trace sources does not automatically
control nontrivial renormalized curvature sources.
Actual YM proof requires a uniform integrability
family or correct source renormalization and
positive-time OS dictionary; the single-group
model is illustrative only.

## F. Current real mass-gap proof state and next main target

Actual accepted physical input:
  Bałaban old/new-R and 4D shell/FP work controls
  named UV activities under published/model hypotheses.
It does NOT construct terminal IR time mixing, nor
full-fibre one-sided leakage, nor uniform renormalized
OS source moments.

The 2026 385-page Hexagon v7 preprint itself declares
whole-continuum-tuning H1 and H2 unfinished; its
Proposition148/Corollary149 is H1 ONLY.

A usable logically noncircular target is:
1. an exact same-Wilson true OS positive-time
   coarse algebra and same-source Schwinger Hamiltonian;
2. new non-Abelian terminal physical-time contraction
   q_IR<1 with a uniform margin (H2);
3. for the continuum-only alternative, sourcewise
   positive-time coarse projection errors controlled
   by full-fibre variance AND conditional leakage,
   after correct renormalization;
4. for original I7 on every finite regulator and
   vacuum-orthogonal sector, also full complement
   compression or Schur cross control with strict margin.

None of (2)--(4) is derived from current true 4D SU2
model bounds. No Lean verification this round.

## G. Closure tree (only original main target, no auxiliary padding)

4D SU2 original I7
├─ GREEN previously strict compiled 39/39 CONDITIONAL main ledger
├─ GREEN OS same-time-source abstract B14 and sourcewise error certificates
├─ GREEN nested conditional variance Pythagoras (66.1)
├─ GREEN quantitative conditional mutual-info sufficient bound (66.2)
├─ GREEN reflection-positive two-time counterexample: full fibre var ->0
│         while positive-time var and OS norm stay nonzero
├─ GREEN bosonic SU2-matrix oscillator comparison (D.2) (paper model only)
├─ YELLOW true positive-time RG fibre/coarse sources and Lp normalization
├─ RED H2: full interacting SU2 terminal IR uniform temporal contraction
├─ RED original I7 complementary sector or genuine Schur bound
└─ OPEN original physical I7 and Clay mass gap.

No conditional lemma or 0+1 toy has been promoted to a solved
four-dimensional physical Yang--Mills estimate.
