# 第74轮｜原4D SU(2) I7纸面主链：最优1/4链路消去＋反射正OS源精确对应（非质量隙证明）

Date: 2026-11-14
Research branch: ym-i7-round74-optimal-os-decimation-20261114
Parent: ym-i7-round73-exact-star-decimation-20261114
Independent executable exact geometry certificate:
  research/i7_round74_optimal_decimation.py
Note: this is a paper-only report with finite parity enumeration; **NO new Lean has been initiated** under the user's explicit paper-first criterion.

## Official status

Original physical I7: **OPEN**.
Historical original 39/39: **CONDITIONAL** (still assumes I7 and other named physical model inputs).
A 4D SU2 Yang–Mills continuum mass-gap theorem has NOT been proved.
All equations below are on the **real finite-cutoff 4D Wilson Gibbs measure**, or its finite-spatial-volume/infinite-time OS reconstruction as explicitly stated; no cactus or simulated reference model is substituted.

## A. NEW optimal link-selection theorem: exactly 1/4 of ALL 4D Wilson links at once

Take an oriented 4D lattice with spatial 3-torus and temporal direction Z
(or periodic even temporal length), with even spatial periods and
all even lengths where periodic. Coordinate directions are
0,1,2 for spatial and 3 for Euclidean time.
At every site x let p(x)=(x0 mod2,x1 mod2,x2 mod2,x3 mod2) in F_2^4.
Define the periodic direction-selector f:F_2^4->{0,1,2,3}
by this exhaustive 4x4 table. Rows are x0x1; columns x2x3:

                 x2x3= 00  01  10  11
          x0x1=00       3   3   0   1
          x0x1=01       2   0   2   1
          x0x1=10       1   2   0   2
          x0x1=11       1   0   3   3

Select precisely the outgoing oriented link e_i(x) for which
  f(p(x))=i.
This selects EXACTLY ONE outgoing link at each site:
  |M|=|V|=|E|/4,
while all links together number |E|=4|V|.

For every elementary plaquette in directions i≠j with base x,
its FOUR oriented-link identifiers are
  e_i(x),e_i(x+e_j),e_j(x),e_j(x+e_i).
Define the number of selected ones
  C(p;i,j) =
   1_[f(p)=i]+1_[f(p⊕e_j)=i]
     +1_[f(p)=j]+1_[f(p⊕e_i)=j].
The table satisfies the FINITE BOOLEAN IDENTITY
  C(p;i,j)=1 for all 16 parity vectors p
                      and all six i<j.
This has been exhaustively checked (96 exact parity incidences),
with the full explicit table and Python certificate.
Hence every real plaquette contains EXACTLY ONE selected edge.

This density is THE MAXIMUM possible among plaquette-independent
link subsets: each selected link belongs to exactly six plaquettes,
each plaquette can contain at most one selected link,
and there are 6|V| plaquettes, so
  6|M|≤6|V| => |M|≤|V|=|E|/4.
Our M ATTAINS this combinatorial bound.
This is 8 TIMES the Round73 old density 1/32, which was
a valid but non-optimal special parity construction.

Exact enumeration on even side length L:
  L=2: |V|=16,  links=64,  selected=16,  plaquettes=96,  hit=96
  L=4: |V|=256, links=1024, selected=256, plaquettes=1536, hit=1536
  L=6: |V|=1296,links=5184,selected=1296,plaquettes=7776,hit=7776
  L=8: |V|=4096,links=16384,selected=4096,plaquettes=24576,hit=24576.
These finite exact checks complement, NOT replace, the 96-case
Boolean certificate valid on any even side length.

## B. More precise induced hypergraph: exact factor degree 18 and incidence 6

On even torus side lengths L>=4:
- for every removed edge e, its six incident plaquettes contain
  3 OTHER retained links each, all 18 distinct;
- for every retained edge r, it belongs to exactly six original
  plaquettes; each has exactly one removed edge; each r therefore
  appears in SIX induced star-factor incidences.

Thus after a single exact decimation:
  |removed-star factors|=|V|,
  |retained links|=3|V|,
  factor support size =18 retained links,
  retained-link star-factor degree =6.
Both local degrees are UNIFORM in volume, not extensive.

This is a precise 18-uniform/6-regular bounded-degree factor hypergraph
for this first-step induced measure. Its diameter is O(1) lattice units.
It is NOT yet a multiscale summability/KP certificate: the
factor potentials grow with beta and their second-stage
couplings need not be small.

## C. Exact true Wilson measure and full source conditional map

Take the original real SU2 Wilson Gibbs density
  dμ(U)∝exp[β Σ_(plaquettes p) tr U_p/2] ∏_(edges e)dHaar(U_e).
For every selected edge e∈M, let s_(e,1),...,s_(e,6)
be the six actual oriented staple unit quaternions
built ONLY from retained links (due unique face hit).
Set h_e=Σ_p s_(e,p)∈R^4.

Every original plaquette has exactly one eliminated link, so
the exponent is EXACTLY
  β Σ_p tr U_p/2
    =Σ_(e∈M) β u_e·h_e(U_R),
with no leftover bare plaquette term.

Define the normalized SU2 partition
  Z(t)=∫_SU2 exp(tu0)dHaar(u)
      =2I_1(t)/t, Z(0)=1.
The true exact retained marginal is
  dμ_R(U_R) ∝∏_(e∈M) Z(β|h_e(U_R)|)
                    ∏_(r∈R)dHaar(U_r),   R=E\M. (74.3)
The full conditional distribution GIVEN ALL retained links is
  μ(dU_M|U_R)=⊗_(e∈M)ν_e(du_e|U_R),
  dν_e(u|U_R)=exp(βu·h_e(U_R))/
                Z(β|h_e(U_R)|) dHaar(u).
This is a factorization of the REAL Wilson measure,
not of an assumed independent plaquette approximation.

For a bounded finite source F define
  (C F)(U_R):=E_μ[F|U_R].
Because conditional variables are independent,
C F is computed exactly by finitely many ν_e integrations.
It is bounded, smooth/continuous in retained links when F is
a finite Wilson word, and gauge invariant if F is:
endpoint gauge covariance of h_e and Haar measure
make conditional expectations commute with local gauge transformations.

For a Wilson word with a SINGLE occurrence of eliminated
U_e, its insertion reduces to the true first moment:
  E_ν(u_e)= A(β|h_e|) h_e/|h_e|,
  A(t)=I_2(t)/I_1(t), with continuous value0 at h_e=0.
For multiple occurrences of one eliminated link,
one must use its full tensor moments (Z derivatives);
C is LINEAR but NOT an algebra homomorphism on overlapping
sources, i.e. generally C(FG)≠(CF)(CG).

## D. The chosen MAXIMAL M is site-reflection covariant and 2-step translation invariant

Let Θ be the site-time reflection
  (x0,x1,x2,t)→(x0,x1,x2,−t).
Spatial edges e_i, i=0,1,2 at time t map to
spatial e_i at −t; time-parity is unchanged.
A temporal edge e_3 at time t maps with inversion
to temporal e_3 at time −t−1, flipping time parity.

Our table has
  f(x0,x1,x2,0)=3 iff f(x0,x1,x2,1)=3
for ALL eight spatial parity triples (indeed only spatial
parities 000 and111 select direction3, and at both time parities).
Therefore ΘM=M exactly.
Also f depends on time only mod2, so τ_2 M=M exactly.

Consequently the true marginal μ_R is:
- gauge invariant,
- Θ-reflection invariant,
- invariant under even time translations τ_2,
- **reflection positive on the retained positive-time
  cylinder algebra**, because any retained positive F
  pulls back unchanged to the original RP measure:
    E_μR[overline(ΘF)F]=E_μ[overline(ΘF)F]≥0.

This is a pure pushforward argument; it assumes
the standard site-reflection positivity of the
original Wilson law with the displayed positive-time
link algebra. It is NOT a claim that every arbitrary
RG projection or every temporal reflection is
automatically reflection positive.

## E. NEW TRUE same-Schwinger OS GRAM SOURCE IDENTITY for the one-step exact decimation

On finite spatial volume and the infinite Euclidean time line,
define the usual site-reflected positive-time link algebra:
- spatial links at integer times t≥0;
- temporal links with both endpoints at t≥0.
Let A^{++} be its STRICTLY positive-time subalgebra
generated by links whose two endpoints have time≥1.
Let A_R^+ be the retained positive-time algebra
(including spatial slice t=0).

A single removed spatial link at t≥1 has six staples
depending only on retained links with time≥0:
adjacent temporal plaquettes touch t−1,t,t+1,
but for t≥1 this never reaches negative time.
A single removed temporal link whose endpoints
lie in t≥1 has staples at t,t+1, also positive.
Therefore for EVERY finite F∈A^{++}:
  C F belongs to A_R^+.
Similarly C(ΘF)=Θ(CF) belongs to the
negative-time retained algebra.
The removed-link supports of ΘF (negative side)
and G∈A^{++} (positive side) are DISJOINT.

Given all retained links, all removed links are
mutually INDEPENDENT by §C. Therefore
  E_μ[overline(ΘF)G | U_R]
    = E_μ[overline(ΘF)|U_R] E_μ[G|U_R]
    = overline(Θ C F) C G.
Integrate over μ_R to get the EXACT equality:
  E_μ[overline(ΘF)G]
    =E_μR[overline(Θ C F) C G].       (74.5)

The same equality holds whenever F or G is a
RETAINED positive-time source (since it has no
removed variables), including t=0 spatial
retained-link observables. Therefore it holds
by linearity on
  D = span(A^{++} ∪ A_R^+).
This subspace is a bona-fide positive-time
physical source space, including all retained
Wilson words and, after time shift, the
full original physical Wilson cylinder algebra.

By Θ and τ2 invariance of M,
  C Θ=Θ C,
  C τ_(2n)=τ_(2n) C
on these applicable source classes.
For positive n:
  E_μ[overline(ΘF) τ_(2n)G]
   =E_μR[overline(Θ CF)τ_(2n)CG].    (74.7)
All pairings use the SAME actual original
Wilson measure and its EXACT marginal, no
synthetic substitution or independently
assumed Schwinger hierarchy.

**Finite-cutoff OS Hilbert consequence.**
Since (74.5) preserves the OS seminorm and its
sesquilinear pairing on D, C descends to an
ISOMETRY between the respective OS quotient
completions. The image contains the retained
positive-time algebra A_R^+ (on which C=identity),
so it is DENSE in the marginal OS Hilbert.
If D is dense in the original OS Hilbert,
the isometry extends to a UNITARY onto the
marginal OS Hilbert.

For the actual finite-spatial-volume Wilson transfer,
one-step strict positive quadratic-form positivity
follows from all Wilson kinetic Peter–Weyl
multipliers rho_j(beta)>0 and invertible
spatial half-magnetic multiplication D.
Hence the one-step selfadjoint physical
transfer T is INJECTIVE and its range is DENSE.
The time shift of the complete positive-time
algebra by one step lies in A^{++}.
Thus D is dense, giving the promised unitary
  J : H_OS(original Wilson) ≅ H_OS(exact marginal)
and the exact TWO-step time-translation intertwining
  J T_original^2 = T_marginal^(2) J
(with the standard normalized stationary
infinite-time transfer on finite spatial volume).
All B08 original time shifts 2n_* microsteps are
even, hence
  J T_original^(2n_*)
    =T_marginal^(2n_*) J.

**Scope guardrail:** this uses site reflection,
the finite-spatial-volume/infinite-time OS
stationary measure and the strict positive
source density; a raw finite-periodic-time
Gibbs correlation is not the vacuum transfer
matrix without the temporal limit.
It does not prove any source-renormalized
cutoff/volume continuum limit or complete
ITERATED RG OS dictionary.
The decimated model may have temporal memory:
T_marginal^(2) need not be a simple
nearest-neighbor transfer.

**Logical implication:** One exact RG
decimation has now been given a true
physical two-step OS/Schwinger source
dictionary, not merely a positive Euclidean
conditional expectation. But UNITARY
equivalence means this RG step by itself
does NOT create a mass gap; its true
physical nonvacuum spectrum is unchanged.

## F. Explicit next-step obstruction: induced interactions are NOT small

The first-step effective action is
  S_eff(U_R) =−Σ_(e∈M) log Z(β|h_e(U_R)|)+constant.
Each factor couples 18 retained links and
each retained link occurs in six factors
at even spatial period L>=4.

At an aligned genuine six-staple background
s_1=...=s_6=I, vary two distinct staples
in a fixed common transverse Lie direction:
s_p(ε)=cosε I +sinε X,
s_q(δ)=cosδ I +sinδ X,
others equalI (unit quaternions).
Then the exact mixed derivative is
  ∂_εδ S_eff |0
   =−β² Cov_(ν_(6β I))(u_X,u_X)
   =−(β/6) A(6β), A(t)=I2(t)/I1(t).  (74.8)
This is NOT small as β→infinity:
  (1/β)∂_εδS_eff ->−1/6.
Even a small-field fluctuation ε~β^(-1/2),
δ~β^(-1/2) produces an O(1) mixed energy.
Numerical Bessel checks:
  β1: −0.1271210; β2.3:−0.3424822;
  β4:−0.6254532; β8:−1.2918883;
  β16:−2.6251097; β32:−5.2917212.

This is a TRUE one-star Wilson effective
interaction. It shows why at a SECOND
elimination stage, removed retained links
that share a factor Z(β|h_e|) cannot be
integrated independently, even when they
do not share an ORIGINAL bare plaquette.
A repeated bare-plaquette-independent
factorization assertion is FALSE.

The effective factor hypergraph bounded
degree (18 supports,6 incidences) is helpful
for setting up a *correct* high-order
polymer/spectral RG ledger but does not
supply any smallness of its physical
nonperturbative terminal IR dynamics.

## G. The remaining irremovable physical red

The original physical I7 requires a
cutoff/volume-uniform strict contraction
at the original fixed physical time
  τ_*=2n_*(a0)*a0:
  <v,T_orig^(2n_*)v> ≤ q_*||v||²,
  0≤q_*<1 on ALL nonvacuum Wilson
  OS/Gauss physical vectors, including
  all mixed roots and toron sectors
  relevant to the original finite graph.

Because of the EXACT OS isometry in §E,
this is equivalent to the same spectral
contraction in the EXACT one-step marginal
model. The new decimation now **removes
the single-step physical SOURCE/OS matching
obligation** under the strict positive-time
hypotheses, but provides no bound q_*<1.

To obtain that bound:
  (i) iterate an exact local/reflection-compatible
      RG to fixed physical scale, controlling
      the induced 18-link factors' overlapping
      supports and higher cumulants;
  (ii) prove a true terminal nonperturbative
       positive-time Dirichlet/Poincare or
       OS spectral inequality uniformly in
       cutoff, volume and all physical sectors;
  (iii) preserve same-source Schwinger
        hierarchy/nontrivial local field
        limit and the original B08 clock.

Existing published Bałaban U1 old/new-R
bounds do NOT currently identify with
all these exact induced factor functions
or produce (ii); the Clay Yang–Mills
mass gap remains unsolved.

Round74 final tree:
4D SU2 I7
├ GREEN previous 39/39 conditional main chain
├ GREEN improved maximal 1/4 physical-link
│       single-step exactly local decimation
├ GREEN 18-support 6-incidence local factor
│       geometry at one real Wilson step
├ GREEN reflection/time2 covariant M
├ GREEN exact conditional source map and
│       REAL OS Gram same-source equality
├ GREEN full finite-regulator OS two-step
│       unitary/time-intertwining
├ GREEN true induced mixed Hessian
│       grows as β/6 in aligned regime
├ YELLOW iterated reflection-compatible
│        high-order real Wilson RG estimates
├ RED full physical terminal H2,
│       uniform T^(2n) spectral margin
└ I7 PAPER OPEN; NO new Lean/CI.

The exact geometry code is in
 research/i7_round74_optimal_decimation.py,
a Python exact parity/plaquette certificate,
not a Lean proof. The complete physical
I7 has NOT been closed on paper, so per
user instruction there is NO new Lean.
