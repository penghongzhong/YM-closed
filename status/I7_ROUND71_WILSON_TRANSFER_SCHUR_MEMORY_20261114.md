# 第71轮｜I7纸面审计：真实Wilson有限时步transfer、Bessel角色谱、时间记忆的精确Feshbach红点

Date: 2026-11-14
Branch: ym-i7-round71-exact-os-memory-20261114
Based on Round70: ym-i7-round70-tree-bridge-bianchi-20261114
Project: 4D SU(2) Yang–Mills U–I–C.

### Absolute acceptance boundary

- True physical I7 remains **OPEN**; no unconditional 4D Yang–Mills continuum mass gap has been proved.
- The historical 39/39 is **CONDITIONAL** and includes explicitly unproved physical I7 / other producer assumptions.
- Round68–70 compact-group plaquette/cactus and interacting-loop gaps are correct only for their **specified Hamiltonian graph or toy classes**. The Wilson Euclidean transfer-to-Hamiltonian model identification was not proved.
- PAPER closure first is the user's policy; **NO new Lean declarations, NO CI** in this round.
- The mathematical results below are exact character-theory, finite reversible-chain, Gaussian Schur-complement and abstract OS operator identities. They are not new physical 4D SU2 dynamical bounds.

## A. Exact Wilson transfer ≠ exp(−a_t * textbook KS Hamiltonian) at finite time step

Use the standard SU(2) Wilson plaquette weight
  w_beta(U)=exp[beta * tr(U)/2],
  beta>0, tr U real, U∈SU2.
Normalize by
  Z_beta=∫_SU2 w_beta(U)dH(U)=2 I_1(beta)/beta,
  k_beta(U)=w_beta(U)/Z_beta.
Let K_beta be Haar-convolution by k_beta:
  (K_beta f)(U)=∫ k_beta(U V^(-1)) f(V)dH(V).

SU2 Peter–Weyl matrix coefficient D^j_mn is an eigenfunction:
  K_beta D^j_mn = rho_j(beta) D^j_mn,
  rho_j(beta)=I_(2j+1)(beta)/I_1(beta), j=0,1/2,1,...
In particular rho_0=1, all rho_j>0. Derivation:
 SU2 class Haar = (2/pi) sin²(theta)dtheta;
 chi_j=sin((2j+1)theta)/sin(theta).
 ∫w_beta chi_j =I_(2j)(beta)-I_(2j+2)(beta)
               =2(2j+1)/beta I_(2j+1)(beta).
 Divide by Z_beta and dim 2j+1 to obtain rho_j.

For a finite spatial-link set E, in temporal gauge the standard
Wilson transfer is built, up to harmless overall scalar,
time-boundary/gauge projection and chosen spatial plaquette
splitting, from
  T_Wilson = P_G * M_beta^(1/2)
                * (⊗_(e∈E) K_beta,e)
                * M_beta^(1/2) * P_G,
where
  M_beta(U_spatial)=exp[(beta/2)∑_(spatial p) tr U_p].
This is positive self-adjoint by the factorization and the exact
positive character coefficients. The normalized physical
one-step transfer is T_Wilson/||T_Wilson|| and the B08
terminal T_* is an appropriate positive integer power
at terminal physical scale; DO NOT identify its logarithm
with a local KS generator without a further argument.

A KS electric Laplacian would have eigenvalues
  eps_j^KS =const * j(j+1).
The true one-step Wilson kinetic energy has
  eps_j^Wilson=−(1/a_t)log rho_j(beta).
For beta→0,
  rho_(1/2)(beta)~beta/4,
  rho_1(beta)~beta²/24,
hence
  [−log rho_1]/[−log rho_(1/2)]→2,
versus the Casimir ratio
  1(1+1)/[(1/2)(3/2)]=8/3.
So **exact finite-step proportionality fails**.
At beta→infinity the ratio tends 8/3,
consistent only with an ASYMPTOTIC continuous-time limit.

Independent Bessel numerical check:
 beta      rho_half     rho_1      eps1/eps_half
 0.10      0.02498959   0.00041641   2.109847
 0.50      0.12371793   0.01025657   2.191570
 1.00      0.24019372   0.03922510   2.270502
 2.00      0.43312743   0.13374515   2.404402
 4.00      0.65804727   0.34195273   2.564248
 8.00      0.81924941   0.59037529   2.643354
 16.00     0.90781485   0.77304629   2.661601

Even if the kinetic sector were exactly exp(−a_t H_E),
the magnetic multiplication M and electric part do not commute:
  [−Δ_SU2, chi_(1/2)(U)] 1
       =(3/4)chi_(1/2)(U) !=0.
Thus the symmetric Wilson transfer product has BCH/logarithm
corrections at a FINITE time step. Its log need not be the
simple local H_E+H_M KS sum. Interacting and temporal
coarse-graining introduces further terms.

The published precise status is in:
- Michael Creutz, Phys Rev D 15 (1977), 1128,
  DOI 10.1103/PhysRevD.15.1128:
  the KS Hamiltonian emerges in the TIMELIKE
  LATTICE SPACING→0 limit of Wilson transfer.
- Martin Lüscher, Commun Math Phys 54 (1977), 283–292,
  DOI 10.1007/BF01614090:
  exact positive selfadjoint Wilson lattice transfer.
- Carena et al, Phys Rev D104 (2021), 094519,
  DOI 10.1103/PhysRevD.104.094519:
  finite-time transfer Trotter/BCH corrections.
- Lüscher–Weisz, Nucl Phys B240 (1984), 349–361,
  DOI 10.1016/0550-3213(84)90270-0:
  generic action improvements can lose ordinary
  one-step physical positivity (so RG effective
  action should not be assumed reflection-positive
  under an arbitrary temporal truncation).

IMPORTANT: Original15Published Lean structure exposes only
  positive: T.IsPositive, vacuumFixed: T Ω=Ω.
It does not prove the Wilson transfer equals
exp(−a_t H_KS), nor the existence of the actual
coarse-gauge source-preserving RG-Hamiltonian dictionary.
The gap is physical-model-specific, not a Mathlib problem.

## B. Fully explicit reversible 3-state counterexample:
## exact coarse projection does not generate a 1-step semigroup

Take three microstates {1,2,3}, uniform stationary measure,
and the real symmetric Markov transfer
  T=[[4/5,1/5,0],
     [1/5,3/5,1/5],
     [0,1/5,4/5]].
Its spectrum is EXACTLY {1,4/5,2/5}, all positive.
The stationary path law is reflection-positive with
the true microscopic OS transfer T.

Observe only the binary coarse variable
  Y=1_{microstate=1}, with centered F=Y-1/3.
Compute exact normalized two-time moments
  M(n)/M(0)
   = (3/4)(4/5)^n+(1/4)(2/5)^n.
In particular
  M(0)=2/9,
  M(1)/M(0)=7/10=0.70,
  M(2)/M(0)=13/25=0.52,
but
  [M(1)/M(0)]²=49/100=0.49 ≠0.52.

A one-dimensional coarse transfer with effective
single eigenvalue 0.70 would predict 0.49 at
two steps; this fails EXACTLY. The visible coarse
process is not first-order Markov, even though
the underlying microscopic model is reversible,
positive-transfer and completely finite.

In the centered 2D Hilbert space,
projection P onto normalized [F] yields
  A=PTP=7/10,
  C=QTQ=1/2,
  ||B||²=||PTQ||²=3/100.
The exact nonvacuum spectrum is {4/5,2/5}, so
the actual slow rate is 4/5 rather than the
apparent one-step 7/10.

This is a rigorous model demonstration that
coarse Wilson observables need not evolve by
P T P as a closed physical semigroup;
the hidden Q-sector can return at later times.

## C. Exact temporal-memory/Feshbach-Schur complement

Now work in the ACTUAL OS vacuum-orthogonal
Hilbert H_perp of a reflection-positive transfer
T, 0≤T≤I, and let P be a true OS orthogonal
coarse projection and Q=I−P (not Euclidean
conditional expectation). In the block H=P H⊕Q H,
  T=[[A,B],[B*,C]],
  A=PTP,C=QTQ,B=PTQ.

Assume ||C||<1 and let Df=I−C>0.
Define exact coarse virtual-return self-energy
  Sigma(1)=B(I−C)^(-1)B*
          =sum_(n=0)^infty B C^n B*≥0.
The sum converges in operator norm, each term
is positive since C≥0. No temporal Markov
closure of the coarse process is assumed.

Complete the square in the FULL nonvacuum form:
  <(x,y),(I−T)(x,y)>
   =<x, (I−A−Sigma(1)) x>
    +||Df^(1/2)(y−Df^(-1) B*x)||².          (71.2)

A rigorous sufficient criterion is therefore:
  Df=I−C≥delta_f I, delta_f>0,
  Dc=I−A−Sigma(1)≥delta_c I, delta_c>0,
with constants uniform in regulator, volume,
terminal RG depth and the relevant full
nonvacuum gauge-sector Hilbert spaces.

Since ||Df^(-1) B*||≤||B||/delta_f,
the triangular change of variables
 y'=y−Df^(-1) B*x gives
  ||(x,y)|| ≤(1+||B||/delta_f)||(x,y')||.
Therefore
  I−T≥delta_eff I,                   (71.3)
  delta_eff=
    min(delta_f,delta_c)/
                (1+||B||/delta_f)² >0.
One may further bound ||B||≤||T||≤1 to
obtain a constant using delta_c,delta_f alone.
Then
  ||T|H_perp||≤1−delta_eff<1,
giving the full original finite complex Wilson
Gram I7 with
  eta_* = delta_eff
and the original B08 generator lower bound
  gap(H_phys)≥−log(1−delta_eff)
           *Lambda_YM/(2c_plus)
under the same actual Wilson transfer/OS
spectral calculus dictionary.

Compare with the Round60 Schur criterion:
if ||A||≤q_c, ||C||≤q_f,
||B||≤eps, then
  delta_f≥1−q_f,
  delta_c≥1−q_c−eps²/(1−q_f).
Hence positivity iff eps²<(1−q_c)(1−q_f).

The new expression identifies the exact *sum of
all virtual fine-field returns* needed in a true
terminal effective theory. It does NOT
estimate them for SU2. Crucially,
  Sigma(1)≥0.
Dropping the fine returns systematically
underestimates the true slow eigenvalue and
can create a FALSE gap certificate.

For the 3-state explicit example in §B:
  Sigma(1)= (3/100)/(1−1/2)=3/50=0.06,
  1−A−Sigma=1−0.7−0.06=0.24;
the true centered T norm is 0.8, not 0.7.

**NOT novelty claim:** Feshbach/Schur-complement
theory is classical. This is a sharper
I7 audit/producer target, not a solution.
For a given OS P, these conditions with
uniform margins are another strong way to
state a physical spectral gap; their hard part
is just as nonperturbative as original I7.

## D. Gaussian exact coarse integration can produce infinite temporal range

Take a strictly positive quadratic action
  S(x,y)=1/2∑_(t∈Z)
   [a x_t²+b y_t²−2c x_t y_t−2h y_t y_(t+1)],
where 0<h<b/2 and a>c²/(b−2h).
The original action has finite nearest-neighbor
temporal range. The y-field Fourier Hessian
is b−2h cos ω>0. Integrating y out EXACTLY
via Gaussian Schur complement gives
  S_eff(x)=1/2∫_(−π)^π
   [a−c²/(b−2h cos ω)] |x_hat(ω)|² dω/(2π).
For h>0, set
  r=(b−sqrt(b²−4h²))/(2h)∈(0,1).
Then the inverse y-kernel is
  G_n=(r^|n|)/sqrt(b²−4h²),
for ALL n∈Z. The effective x action
has a nonzero coupling −c² G_n
at arbitrarily large temporal separation.
All formulas are exact and require no mass-gap
hypothesis. They do NOT identify the RG
SU2 Wilson effective kernel with Gaussian data;
they falsify the shortcut
  "local microscopic action => nearest-neighbor
   blocked transfer after eliminating fine fields".

This complements the positive-transfer
3-state counterexample, which is also OS-like.

## E. Consequence for genuine 4D SU2 I7:
## one irreducible physical producer, not a new inventory of lemmas

The Round68–70 local SU2 compact plaquette,
interacting multi-loop and cactus-graph KS
gap proofs hold for their explicit spatial
Hamiltonian models only. They cannot be
transported to the ORIGINAL isotropic
Wilson positive transfer unless the exact
temporal source/RG/OS dictionary and a
volume-uniform spectral/form comparison
are proved.

A corrected finite-terminal bridge can
target the ACTUAL normalized Wilson T_{*,k}
of Original15/B08 and true OS P_k:
  (i) Q-sector return resolvent is
      uniformly controlled:
      I−Q T_* Q≥delta_f I;
  (ii) full coarse effective Dirichlet
      including temporal memory has margin:
      I−P T_* P
         −P T_* Q (I−Q T_* Q)^(-1)
                       Q T_* P
      ≥delta_c I;
  (iii) exact same true SU2 Wilson source
      and RP OS vacuum/Gauss sectors match,
      with uniform bounds over regulator,
      volume and cutoff/exhaustion.
Only then the paper Feshbach bound (71.3)
gives original I7 and original16 mass gap.
These (i),(ii) are UNPROVED in the true
nonperturbative terminal Wilson sector.

Unlike an inferred effective KS generator,
this route respects the exact
Wilson transfer even at finite time step
and does not discard induced time memory.
It does not assume q_IR as an arbitrary
independent "external published theorem".

## F. Formal closure tree / no Lean

4D SU2 original I7
├── GREEN 39/39 historical CONDITIONAL
├── GREEN exact SU2 Wilson kinetic
│       character spectrum rho_j=I_(2j+1)/I1
├── GREEN finite time KS equality disproved
│       (ratio 2 vs 8/3 as beta->0)
├── GREEN true finite reversible 3-state
│       coarse-process non-Markov example
├── GREEN exact Schur/Feshbach memory producer
│       and positive self-energy
├── GREEN positive gap from delta_f,delta_c
│       independent of spatial volume
├── GREEN finite-time Gaussian integration
│       induces long-range temporal memory
├── YELLOW match physical OS RG coarse P,
│       full Gauss sectors and Wilson tests
├── RED true full SU2 terminal delta_f>0,
│       delta_c>0 uniformly over parameters
├── then physical original complete Gram I7,
│       original16/42 conditional final path,
│       ONLY THEN new Lean verification
└── I7 PAPER OPEN, NO NEW LEAN, no Clay solution.
