# 第73轮｜真实4D SU(2) Wilson正密度链路精确消去、全配置非线性staple束缚及时间卷积障碍

Date: 2026-11-14
Branch: ym-i7-round73-exact-star-decimation-20261114
Based on ym-i7-round72-true-wilson-doob-cactus-20261114.

## 0. Required proof status

The original physical I7 **IS NOT CLOSED ON PAPER**. The historical 39/39 main statements are CONDITIONALLY VERIFIED and still explicitly assume I7. The full 4D SU(2) Wilson/OS physical-time transfer uniform gap is **OPEN**; Clay's continuum existence/gap likewise OPEN.

According to the user's rule, do NOT initiate new Lean declarations or official CI until the actual physical I7 paper proof is complete. The exact finite group identities and inequalities below are paper-closed partial physical Wilson-model results only. Numerical code is a consistency check, NOT a proof.

## 1. Full 4D Wilson six-staple exact integral and gauge-invariant pairwise energy

Identify SU(2) with unit quaternions S³⊂R⁴, with
  (1/2)tr(UV)=u · bar(v)
once quaternion conjugation/orientation is fixed.
For a genuine interior 4-dimensional hypercubic Wilson link
e, exactly six plaquettes contain e: 2(d−1)=6.
Fix all other link variables in the Wilson Gibbs density
  exp[ β Σ_p (1/2)tr U_p ], β>0.
For each p containing e, its three-link oriented staple
determines a unit vector s_p∈S³ such that
  (1/2)tr U_p= u_e·s_p.
These s_p transform together under the endpoint
gauge transformations; their mutual Euclidean
chord distances are gauge invariant.

Define h=∑_(p=1)^6 s_p.
Using normalized Haar on S³, define
  Z(t)=∫_S³ exp(t u_0)dH(u)=2 I_1(t)/t, Z(0)=1.
Then the EXACT finite-volume conditional integral is
  ∫_SU2 exp(β u_e·h)dH(u_e)=Z(β |h|).   (73.1)

Define the complete-graph staple dispersion
  E_6=Σ_(p<q)||s_p−s_q||².
Because ||s_p||=1 and m=6,
  ||h||²=6²−E_6=36−E_6.
The exact relative induced effective action is
  Delta S_6(E_6)
    =log Z(6β)−log Z(β sqrt(36−E_6)).  (73.2)
No independence of plaquettes, small-field chart,
RG polynomial truncation, or external IR input
is used. The identity holds for ANY realizable
true Wilson staple background.

More generally for m≥1 unit-vector staples:
  ||Σ_p s_p||²=m²−Σ_(p<q)||s_p−s_q||².
This identity is a purely Euclidean S³ geometry
and does not change the original Wilson source.

## 2. Closed global nonlinear coercivity bound valid for ALL backgrounds

Let A(t)=I_2(t)/I_1(t)=d/dt(log Z(t)), t>0.
The exact Riccati equation is
  A'(t)=1−A(t)²−3A(t)/t.

Upper bound A(t)≤t/4:
expand I_2(t) and (t/4)I_1(t) in
nonnegative powers of t; coefficientwise
  1/(k+2)! ≤1/[2(k+1)!]
for k≥0. Hence I2≤(t/4)I1, strict for t>0.

Lower bound A(t)≥t/(t+4):
set s(t)=t/(t+4). Near zero the Bessel series
  A=t/4−t³/96+O(t^5),
  s=t/4−t²/16+O(t³)
gives A>s. At every hypothetical first
touching point A=s with t>0,
  [1−s²−3s/t]−s'
  =5t/(t+4)²>0.
A solution cannot cross from A>s to A<s
at such a point; hence A≥s globally.

Let E∈[0,m²], r=sqrt(m²−E).
Then by the fundamental theorem of calculus,
  Delta S_m(E)
     =∫_(r)^m β A(β q)dq.

Using
 βq/(βq+4) ≤ A(βq) ≤ βq/4,
and βq+4≤mβ+4 for q≤m, we derive
  beta²/[2(m beta+4)] * E
    ≤ Delta S_m(E)
    ≤ beta²/8 * E.                            (73.3)

In the ACTUAL 4D six-staple Wilson star m=6,
  [β²/(12β+8)] E_6
       ≤Delta S_6(E_6)
       ≤[β²/8] E_6
for EVERY β>0, ANY gauge-compatible backgrounds.
A negative effective energy sign error would
invalidate this conclusion; the full eliminated
Gibbs weight is proportional to
  exp[-Delta S_6(E_6)].
It always favours mutual staple alignment.

This is genuine local coercivity, not a
UNIFORM TEMPORAL TRANSFER gap. Even if all
staples have the SAME group value different from
the identity, E_6=0, and this one-star induced
action costs zero relative energy. Common
orientation modes are unpenalized by this
single-link relation and may reflect gauge
freedom; they must not be identified
uncritically with physical massless excitations.

## 3. New genuine Wilson RG step: a POSITIVE DENSITY 1/32 of actual links can be eliminated EXACTLY together

On a 4D periodic hypercubic lattice with even
lengths in directions 2,3,4, orient links in
directions i=1,...,4 (any consistent convention).
Select M to be all links oriented along
direction1 whose base coordinates x2,x3,x4
are each even modulo2. This contains
exactly #V/8 links, which is density 1/32
among the 4#V oriented spatial+temporal links.

Any elementary plaquette containing direction1
contains exactly TWO links oriented along
direction1, at bases differing by one step in
one of the transverse directions. Their
transverse parities are opposite. Therefore
EVERY plaquette contains AT MOST ONE member of M.
All other plaquettes contain zero selected edges.
For cubic periodic size L even, explicit exact
enumeration checked:
  L=4: #M=32 out of 1024 links, overlaps=0;
  L=6: #M=162 out of 5184 links, overlaps=0;
  L=8: #M=512 out of 16384 links, overlaps=0.

Because no plaquette contains two removed
edges, the original 4D Wilson Gibbs exponent
splits, exactly and with no approximation:
  β Σ_p (tr U_p/2)
  =β Σ_(p∩M=∅) tr U_p/2
       +Σ_(e∈M) β u_e·h_e(U_(E\M)),
where each h_e is the six-staple sum built
EXCLUSIVELY from retained links.

Consequently integrating all removed links
in product Haar EXACTLY produces
  density_eff(U_(E\M))
    ∝exp[β Σ_(p∩M=∅)tr U_p/2]
      ∏_(e∈M) Z(β|h_e|).

Equivalently the effective action is
  S_eff=
   −β Σ_(p∩M=∅)tr U_p/2
   +Σ_(e∈M) Delta S_6(E_{6,e})
   −|M| log Z(6β) + constant.           (73.6*)

This is an honest **positive-density, full
four-dimensional SU(2) Wilson decimation**.
No spurious independent plaquette assumption,
no omission of the cubic Bianchi constraints,
no crossing of "original dynamics" to
cactus/toy Hamiltonians. All induced staple
terms are exactly local around their
removed original link at THIS first step.

Gauge invariance holds because each E_{6,e}
is made from pairwise Euclidean chords of
staples with common endpoint gauge action.
The decimated measure is the marginal of
the TRUE Wilson measure, and hence preserves
all expectations for observables that use
only retained links.

Reflection positivity is also inherited for
the retained positive-time algebra if the
selected M is invariant under the chosen
reflection Θ and the original positive-time
subalgebra pulls back to itself: simply
  ∫ conj(ΘF)F dμ_eff
     =∫ conj(Θ(F∘p))(F∘p)dμ_original≥0.
For a site reflection reversing the fourth
coordinate, even time parity is preserved
by the above M; precise link-reflection and
Original15 OS test geometry must still be
matched before using this as a physical
transfer identification.

**Critical limitation:** after the first
decimation, the induced interactions involve
multiple retained links. A second identical
plaquette-separated factorization cannot
be asserted without a new exact
interaction-support analysis. The positive
alignment cost does not provide a terminal
IR mass scale or a cutoff-uniform q<1.
No original I7 paper closure follows.

## 4. Exact local source response and true single-link covariance

For h in R4, let ν_(β h) be the true
single-link conditional law
  dν_(β h)(u)=exp(βu·h) dH(u)/Z(β||h||).
Then for h≠0,
  E_(ν_(βh))u =A(β||h||) * h/||h||.
Let \hat h=h/||h||, t=β||h||.
The complete ambient R4 covariance is
  Cov(u)
   =A'(t) \hat h\hat h^T
      +[A(t)/t](I−\hat h\hat h^T),
  A'(t)=1−A(t)²−3A(t)/t.
At h=0, Cov(u)=I_4/4.

Moreover,
  D_h² log Z(β||h||)=β² Cov_(ν_(β h))(u)
is positive semidefinite.
This is an EXACT **one-fibre**
Hessian/covariance identity of the
actual Wilson model and a local illustration
of the general effective-action
force-covariance formula from Round64.
It does NOT bound covariance under the
FULL terminal fibre measure including all
remaining spatial-temporal links and
their IR effects.

## 5. Exact time-convolution/magnetic-dressing ratio for ALL four spatial staples

Now select a SPACE link at a fixed time
slice. Its four SPATIAL plaquettes contribute
to the half-magnetic transfer dressing
  D_h(u)=exp[(β/2)u·h],
where h=Σ_(p=1)^4 s_p∈R4, |h|≤4.
The genuine normalized one-link Wilson
temporal convolution K_beta has kernel
  k_beta(u,v)=exp(βu·v)/Z(β).
Then EXACTLY
  (K_beta D_h)(u)/D_h(u)
    = Z(β||u+h/2||)/
       [Z(β)exp((β/2)u·h)].             (73.4)

At h=4u (four staples aligned with
the link variable),
  R_flat=e^(-2β) Z(3β)/Z(β)
          ->3^(-3/2).
At h=−4u (all four staples anti-aligned),
  R_bad=e^(2β) EXACTLY
because K_beta D_{−4u}(u)=1.
All such configurations are allowed
by the local group-link geometry, though
they are statistically suppressed in
the low-action weak-coupling ensemble.

In fact this is the global maximum:
for fixed u the mapping h→R(h) is
a moment generating function
  R(h)=E_(v~K_beta(u,dv))
          exp[(β/2)(v−u)·h],
hence it is convex in h.
Its maximum on the closed ball |h|≤4
occurs on the sphere |h|=4.
Write h=4a, |a|=1, z=u·a∈[-1,1].
Then
  R(z)=e^(−2βz)
        Z(β sqrt(5+4z))/Z(β).
Using A(t)=Z'(t)/Z(t)∈(0,1),
  d/dz log R
   =2β[A(βsqrt(5+4z))/sqrt(5+4z)−1]<0,
because sqrt(5+4z)≥1.
Thus R maximizes at z=−1 and
  sup_(u,s1...s4)R=e^(2β).             (73.5)

This explicitly rules out a regulator-uniform
pointwise o(1) comparison between the
spatial magnetic half-dressing and
the exact one-link time convolution
as β(a0)→infinity.

Sample exact Bessel checks:
 β     flat R       global sup R
 1     0.3155633     7.3890561
 2.3   0.2269290     99.4843156
 8     0.1991518     8886110.52
 32    0.1939920     6.235149e27.

The pointwise maximum can occur on rare
large-action configurations; failing a
POINTWISE comparison is NOT a lower bound
on the physical massless spectrum, nor
does it rule out an integrated estimate
with the correct interacting ground state.

## 6. Weak-coupling near-aligned scaling: an O(1) shared-edge effect survives even inside the small-field chart

For m distinct 4D Wilson staples, use
  s_p(β)=(sqrt(1−||xi_p||²/β), xi_p/sqrtβ)
for fixed vectors xi_p∈R³ and β sufficiently
large that ||xi_p||²<β.
Then
  E_m(β)
    =β^(-1) Σ_(p<q)||xi_p−xi_q||² +O(β^(-2)).
Using the large-t Bessel partition asymptotic,
  log Z(t)=t−(3/2)log t+const+O(t^(-1)),
the true one-edge induced action satisfies
  lim_(β→infinity) Delta S_m(E_m)
    =[1/(2m)]Σ_(p<q)||xi_p−xi_q||²
    =(1/2)Σ_p||xi_p−mean(xi)||².        (73.7)

For m=6 the explicit Gaussian limit
coefficient is 1/12; the Hessian is
the orthogonal projection onto the
3(m−1)-dimensional relative-staple
fluctuation space. The three-dimensional
common-orientation subspace costs zero
in this ONE-EDGE local effective action,
and may correspond to gauge redundancy.
No physical massless degree of freedom
is inferred from that local zero mode.

Numerical explicit six-staple test:
  xi=(e1,e2,−e1,−e2,e3,−e3);
  Σ_(p<q)||xi_p−xi_q||²=36,
so the exact limiting induced action is 36/12=3.
 β=50:  Delta S=3.0000126045,
 β=200: Delta S=3.0000007829,
 β=1000:Delta S=3.0000000313.

For the SPATIAL m=4 time-dressing ratio,
fix u=(1,0,0,0) and let
s_p=(sqrt(1−||xi_p||²/β),xi_p/sqrtβ).
Then direct expansion of (73.4) gives
  lim_(β→infinity)R_beta(u,h)
    =3^(-3/2) exp[||Σ_p xi_p||²/24].     (73.8)
Even if every individual staple tends to I
at rate β^(-1/2), the relative mismatch
need not tend to1. Taking all xi_p=v,
|v|=2, gives the limit
  3^(-3/2)*exp(8/3)≈2.76972554 >1.
So not only rare far-from-identity
configurations, but some nontrivial
weak-field scaling windows invalidate a
pointwise contraction conclusion.

## 7. Executed numerical consistency checks (not mathematical proof)

A local Python+mpmath runner, 'i7_round73_star_check.py',
was executed with fixed seed 73. It checked:
- 400 random m=4 and 400 random m=6
  SU2 staple configurations over beta
  0.1,1,2.3,8,32 against both sides of (73.3):
  all 800 satisfied the exact proven inequalities;
- beta=1,2.3,8,32 flat vs worst magnetic
  ratios (73.4)–(73.5);
- scalar Bessel ratio bounds A(t)
  for t=0.1,1,4,32;
- six-staple Gaussian scaling (73.7).
The executed script is separate from Lean,
and no finite number of numerical tests
is claimed to verify the Clay problem.

## 8. Proper main-chain assessment: what is new and what remains red

The positive-density single-step decimation
and (73.3) are exact statements on the
REAL 4D SU2 Wilson Gibbs measure. This
is more physically grounded than the
Round66 noncompact matrix oscillator
and Round68–72 special cactus-graph
comparators.

However original I7 is a **fixed physical
time nonvacuum transfer contraction** for
the full same-regulator SU2 Wilson model.
The exact one-link star matching energy
does NOT prove:
 (a) full four-dimensional spatial-temporal
     multi-scale RG can be iterated with
     cutoff/volume uniform constants;
 (b) the completely induced, possibly
     temporally nonlocal effective interactions
     yield a positive physical H2 time gap;
 (c) a cutoff/volume uniform
     nonvacuum Poincare inequality in
     the EXACT Wilson ground-state Doob law
     π=ψ²dH (Round72);
 (d) same-Schwinger/OS renormalized local
     source nontriviality and B08 fixed
     physical-time matching;
 (e) control of every Gauss/center/toron
     physical sector after the prescribed
     infinite-volume/continuum limits.

At large beta the local inequality is
stronger, with lower alignment stiffness
beta/(2m) per fixed unscaled chord
dispersion, but this is not a temporal mass:
the correct small-fluctuation scaling
produces an O(1) quadratic relative-staple
action, not a uniform physical H2 gap.

One non-circular immediate mathematical
next task is to build a reflection-stable,
multi-stage exact RG decimation in which
the induced multi-link interaction
supports remain controlled and prove
a SOURCE-MATCHED temporal Dirichlet
comparison for the same true Wilson
Doob P_*(a0). The present one-step
positive-density decimation solves NONE
of those long-range IR estimates.

## 9. Round73 closure tree

4D SU2 original I7
├─ 🟢 historical original 39/39 CONDITIONAL retained
├─ 🟢 exact actual 4D Wilson six-staple one-edge integral
├─ 🟢 gauge-invariant complete-graph staple dispersion identity
├─ 🟢 global all-background nonlinear alignment coercivity
│       β² E/(12β+8) ≤ Delta S_6 ≤ β² E/8
├─ 🟢 actual full 4D positive-density 1/32
│       plaquette-separated simultaneous exact decimation
├─ 🟢 explicit single-link SU2 fibre covariance/Hessian
├─ 🟢 exact temporal spatial-dressing ratio for four staples
│       sup R=e^(2β), flat R→3^(−3/2)
├─ 🟢 Gaussian small-field limit of induced star action
│       ∆S6→Σ||xi_p−xi_q||²/12, not a mass gap
├─ 🟡 multi-stage reflection-compatible RG support/source dictionary
├─ 🔴 true full cubic Wilson ground-state temporal Dirichlet
│       margin η_*(a0,Volume)>=η0>0
│       with the original B08 physical clock and all sectors
├─ then true physical I7 paper closure
├─ only then restart Lean verification
└─ I7 PAPER OPEN; NO new Lean, NO Clay claim.

Relevant published/model context:
Osterwalder–Seiler, Ann.Phys.110 (1978), 440–471.
Lüscher, CMP54 (1977), 283–292 (positive transfer).
Bhattacharjee et al., "One Cube Estimate Implies the
Yang–Mills Mass Gap", v7 (2026),
https://hexagonmath.org/2610.00341v7,
explicitly states the full continuum-tuning
physical cube estimate remains UNPROVED.


## 10. NEW exact LOCAL HARNACK control for the TRUE finite Wilson transfer ground state (volume independent)

Work on any finite spatial 3D lattice
with the full (before gauge projection)
Wilson transfer
  T = D K D,
  K=⊗_(spatial links e) K_beta,e,
  D(U)=exp[(β/4)Σ_(spatial p)tr U_p].
The strictly positive, compact, symmetric
integral kernel has a unique positive
Perron eigenfunction ψ:
  λ0 ψ(U)=D(U) ∫ K(U,V)D(V)ψ(V)dV.
Gauge equivariance and uniqueness make
ψ gauge invariant, so this is also the
physical gauge-invariant vacuum when
restricting to the Gauss sector.

Fix two configurations U,U' that differ
ONLY on a single spatial link e. Let
d=||u_e−u'_e||_{R4}∈[0,2].
In 3D, the interior spatial link belongs
to exactly FOUR spatial plaquettes.
With all other links held fixed,
  log D(U)=(β/2)u_e·h_e +const,
  ||h_e||<=4.
Therefore
  |log D(U)−log D(U')|<=2βd.           (73.9a)

For any integration variable V,
the full product temporal Wilson kernel
differs only by the one-link factor:
  K(U,V)/K(U',V)
    =exp[β(u_e−u'_e)·v_e].
Thus uniformly in V,
  e^(−βd)<=K(U,V)/K(U',V)<=e^(βd).    (73.9b)

Multiplying this ratio bound by the
strictly positive D(V)ψ(V) and integrating,
then using the Perron eigenfunction
equation, yields EXACTLY
  |log ψ(U)−log ψ(U')|<=3βd.           (73.9)

No spectral-gap assumption, no global
Haar density comparison and no input
about the time continuum limit is used.
The estimate is independent of the
number of spatial links and plaquettes
at any fixed β. At boundary links with
fewer spatial faces, the constant is
smaller.

Now the true stationary vacuum slice
measure is π(U)=ψ(U)^2 dHaar^E.
For any fixed remaining spatial links,
the conditional density in U_e has
ratio between any two link values
bounded by e^(12β) because d<=2:
  sup p_e/inf p_e<=e^(12β).
After conditional Haar normalization,
  e^(−12β)<=p_e(u)<=e^(12β)           (73.10)
for all u∈SU2 and all other links,
independent of spatial volume.

With the SU2 Haar Laplace/Poincare
first nonzero eigenvalue 3/4, the
conditional ground-slice one-link
Poincare bound also follows by a
standard Holley–Stroock weighted
comparison:
  Var_(π_e)(f)
     <=(4/3)e^(12β)
                ∫||∇_e f||² dπ_e.     (73.11)
Here ∇_e and −Δ_e must share the SU2
Casimir normalization λ1=3/4.

This is an ACTUAL finite-volume
Wilson physical-ground-state result.
It avoids the e^(−c volume) losses
of the previous GLOBAL density method.
But its constant degenerates at bare
UV weak coupling β(a0)→infinity, and
it is only a SINGLE-LINK conditional
Poincare inequality, NOT a global
physical-time OS transfer gap.

### Exact local conditional update of the TRUE Doob Markov transfer

From Round72, P(U,dV) =
  K(U,V) w(V)/(Kw)(U)dV, w=Dψ.
Fix initial U and all next-slice
links V_(f≠e). The conditional
density of the remaining next
link v_e is proportional to
  k_beta(u_e,v_e) w(v_e,V_-).
The logarithm of k changes by
at most β d(v,v').
Since log w=log D+log ψ, its
one-link Lipschitz bound is at
most (2+3)βd=5βd.
Hence the true one-step next-link
conditional kernel, GIVEN all
other next-slice values, has
  |log density(v)−log density(v')|
      <=6β ||v−v'|| <=12β.
Its normalized density relative
to Haar is therefore >=e^(−12β),
a VOLUME-independent local
one-step refresh lower bound.

As in low-temperature spin systems,
all single-site conditional
refresh probabilities can be
positive and volume-independent
while global spatial-time mixing
still slows to zero due to collective
metastability or boundary sectors.
A Dobrushin/large-block condition
on dependencies of the ACTUAL
Doob w or another true IR H2
estimate is still required.

These are paper identities; they
do NOT establish original 4D SU2
physical I7, nor a cutoff-uniform
η* at the B08 physical clock.

## 11. Updated shortest physical main chain

🟢 real full 4D Wilson 1/32 independent-link decimation exact
🟢 SU2 all-background one-star nonlinear pairwise alignment coercivity
🟢 exact true finite-time Wilson magnetic ratio sup=e^(2β)
🟢 exact actual physical vacuum local-Harnack,
   one-link conditional density and local Poincare,
   volume-uniform for each fixed beta
🟡 iterate exact RG with reflection/positive-time
   source, Gauss, Bianchi and all-volume control
🔴 full 4D cubic nonperturbative physical-time
   Dirichlet/OS transfer gap η*>=η0>0 uniformly
   as β(a0)→infinity and physical volume grows
→ only then original I7 paper closure
→ only then new Lean acceptance.

Historical 39/39 CONDITIONAL unchanged.
I7 PAPER OPEN. NO NEW LEAN / CI.
