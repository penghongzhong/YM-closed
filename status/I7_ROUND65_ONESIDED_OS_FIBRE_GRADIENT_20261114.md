# 第65轮：I7 纸面闭合审查——正时间 OS 投影、纤维方差及低频谱模态

Date: 2026-11-14
Branch: ym-i7-round65-os-one-sided-20261114
Base: ym-i7-round64-paper-only-20261114 / 15324253da9a3c0ec0e6228be8e57e6d7e71282e

## 正式审计状态

原始 4D SU(2) Yang–Mills I7 = **OPEN**。
原稿历史 39/39 = **CONDITIONAL**，此计数不增不减。
第59、63轮 B14 同网极限和源依赖误差条件性 Lean 结果保持；本轮严格遵守“纸面未闭合不启动新 Lean”的用户指令：没有创建、运行、修改新的 Lean 声明或 CI。
本轮新结果是精确的抽象 OS/L2 投影桥、线性自由场模式计数及既有非微扰预印本的严格输入范围复核，而不是真实 SU(2) 质量隙。

## 1. 第64轮两压缩判据的必要降级：过强，不是最短普适路线

对实际真空正交 OS Hilbert 空间的正自伴收缩 T、正交投影 P 和 Q=I-P，原第64轮纸面引理正确证明
  ||T|| <= q_c+q_f,
如果 ||PTP||<=q_c、||QTQ||<=q_f。

但是该充分条件可能太强：
  T=diag(0.9,0.4), P=diag(1,0)
有真实 ||T||=0.9<1，但 q_c+q_f=1.3>1。
因此若 q_c+q_f>=1，必须保留原第60轮的实际交叉 Schur 判据：
  eps=||PTQ||,
  q_eff=(q_c+q_f+sqrt((q_c-q_f)^2+4eps^2))/2,
  eps²<(1-q_c)(1-q_f).
两项正性压缩自身不再足够。

用 q_c=0.9、q_f=0.4：
  eps=0     -> q_eff=0.9
  eps=0.1   -> q_eff=0.91925824
  eps=0.2   -> q_eff=0.97015621
  eps=sqrt(0.06) -> q_eff=1.
故独立交叉项小性不能在所有有效模型里删除。
原第64轮结论仅在 q_c+q_f<1 时保留为便捷短路线。

## 2. 核实论文提出的完整真实纤维力协方差目标

Reviewed the PDF and actual screenshots of pp.79--80, and pp.200--201:
Deep Bhattacharjee, Ushashi Bhattacharya, James Montgomery Lockwood,
Tristan Romanov, *One Cube Estimate Implies the Yang–Mills Mass Gap*,
v7 (4 November 2026), https://hexagonmath.org/2610.00341v7.
This is a preprint, not independently certified peer-reviewed model closure.

Let ζ_V be the exact full conditioned SU(2) Wilson fibre law for
straight-path RG, and
  K_(e,e')=sup_V sup_(||X||=||Y||=1)
    |Cov_(ζ_V)(D_X^(a_e) S,D_Y^(a_e') S)|
for distinct marked coarse links.
Proposition 148 derives the off-diagonal Hessian identity and relates
the Dobrushin coefficient to (D²/4) K_(e,e').
For SU(2) under that paper's geodesic metric D=√2 π, so D²/4=π²/2.
Corollary149's full **uniform-in-volume, uniform-in-cutoff** criterion is
  (π²/2) sup_j ∑_(e≠j)K_(e,j) <= c<1,
  (π²/2) sup_j ∑_(|Δ∞(e,j)|>R)K_(e,j)
      <=(1-c)/16,   R>=1.
In particular the first row sum must be <2/π²≈0.2026424,
and the distant sum must be <=(1-c)/(8π²).

As a numerical target, c=1/2 gives
  sup_j∑_(e≠j)K_(e,j) <=1/π²≈0.10132118,
  distant sum <=1/(16π²)≈0.006332574.
This is strictly more precise than merely asserting an unspecified
q_IR<1.

The preprint itself explicitly marks these full conditioned
force covariances and the all-tuning/all-volume criterion OPEN.
The public Original24_BalabanTwoRootRealFullSeries.lean controls named
old/new-R connected Mayer amplitudes, not K_(e,j). The full
conditioned-fibre source dictionary and weighted row summability are
missing. Exactness of an individual connected two-root expansion
does not by itself imply the needed nonperturbative full-fibre bound.

**Pointwise-to-row obstruction:** for M coarse links define
  K_(i,j)=1/M for i≠j, K_(i,i)=0.
Every entry tends to zero as M→∞, but
  ∑_(i≠j)K_(i,j)=(M-1)/M→1.
Therefore estimates uniform on bounded-size tori or fixed marked
pairs cannot be promoted to the row sum without true spatial
summability. This also applies if the conditional force covariances
are estimated on typical coarse configurations rather than
the supremum over all V used in Proposition148.

## 3. NEW exact OS-positive-time approximation lemma (PAPER CLOSED)

Let μ_k be the actual reflection-invariant Wilson probability,
A_(+,k) its positive-time L² observable space, and [F]_OS the
Osterwalder--Seiler quotient vector with norm
  ||[F]||²_OS=E_μ[conj(ΘF) F]>=0.
By ordinary Cauchy--Schwarz and Θ-invariance,
  ||[H]||_OS <= ||H||_(L²(μ))
for every positive-time H.

Let C_(+,k) be a closed subspace of *positive-time coarse*
Euclidean cylinder observables, and define K_(k,coarse) as the closure
of their centered OS equivalence classes inside the true OS
vacuum-orthogonal Hilbert space.
Its Hilbert orthogonal projection P_(k,OS) exists regardless of
whether Euclidean conditional expectation itself acts on the OS
quotient.

For any centered positive-time F and positive-time coarse
G in C_(+,k), best approximation and OS/L² contractivity give
  ||(I-P_(k,OS))[F]||_OS
    <=||[F-G]||_OS
    <=||F-G||_(L²(μ)).                          (65.2)

Unlike a previous invalid shortcut, we do **NOT** require
P_(k,OS)=E_μ[·|B] on the OS Hilbert space.

If C_(+,k) is the complete L² of a positive-time coarse
sigma algebra B_(+,k) subset A_(+,k), the Euclidean best
approximant is G=E[F|B_(+,k)], which is positive-time;
  ||F-G||²_2
    = E[Var(F|B_(+,k))].
Hence
  δ²_(k,F):=||(I-P_(k,OS))[F]||²_OS
      <= E Var(F|B_(+,k)).                      (65.6)

This is a strictly correct model-independent bridge, with no
identification of Euclidean P_B with physical OS orthogonal P.

**Subtle missing input:** Theorem 363 of the external preprint
controls a chart-restricted fibre conditioned on the FULL coarse
configuration (including times on both sides of reflection).
The conditional variance given only B_+ is generally LARGER.
One cannot substitute the published full-fibre Poincaré
constant into (65.6) without a genuine *one-sided/reflection-adapted*
fibre conditional inequality. The latter is a new precise
model-analytic RED; also its chart complement and normalizing
densities must be controlled in the original Wilson measure.

## 4. Positive transfer + approximate coarse source gives continuum B14

Suppose the actual nonvacuum T_k is a positive selfadjoint
contraction and the true OS projection P_k above satisfies
  ||P_k T_k P_k|| <= q_c<1
uniform in cutoff/volume on the coarse subspace, where q_c is
independent of the physical Wilson source.

Write v_k=[F_k], x=P_k v_k, y=(I-P_k)v_k.
By the Cauchy--Schwarz inequality for the positive operator T_k,
  <v,Tv>
    <=(sqrt(q_c)||x||+||y||)^2
    <= q_c||v||²+2sqrt(q_c)||v||δ_(k,F)+δ_(k,F)².
If a fixed source F has bounded ||v_k||<=M_F and
  E Var(F_k|B_(+,k)) ->0
on the SAME joint cutoff-volume filter, then
  Qt(k,F) <= q_c Q0(k,F) + err(k,F),
  err(k,F):=2sqrt(q_c) M_F δ_(k,F)+δ_(k,F)² ->0.

The formally accepted Round63 theorem
  b14_continuum_gap_from_sourcewise_error
(CI 43563378310)
then yields continuum gap >=-log(q_c)/t, CONDITIONALLY on
same-source OS/Schwinger identity, fixed physical time,
positive heat spectral calculus, and density of the selected
physical test algebra.

This **does not close the original finite-regulator I7**.
It also does not produce q_c or true one-sided variance decay;
both remain genuine nonperturbative model obligations.

## 5. Theorem330/363's quantitative scope and the bare-Wilson gradient loss

The same v7 preprint Theorem330 claims the finite-volume-uniform
linearized block-fibre coercivity after block-tree gauge:
  ∑_e |φ_e|² <=52 ∑_p|(dφ)_p|²,
on the kernel of the four-dimensional side-two block averaging
maps, with the appropriate fixed tree links.
This is for a Gaussian/linearized fibre, not a statement about
the full quantum OS Hamiltonian.

Theorem363 claims a true non-Abelian SU(2) convex-chart
Brascamp--Lieb bound
  Var_(ζ_chart)(F) <= (60/λ) E|∇_fib F|²,
λ=β_W/4, hence constant 240/β_W.
This is for the chart-restricted conditioned law, in the
stated tiny-small-curvature and sufficiently-large-β range.
The displayed SU(2) sufficient constants on p.201 require
β_W>=2.3e17 and curvature/chart radius about <=6e-13,
and are NOT generic all-background inequalities.
The set outside the good chart also needs separate control.

A centered Wilson trace around a simple loop of m microscopic
links is uniformly bounded in absolute value, yet a naive
product-rule derivative bound only gives
  ||∇_links W||² <= C*m
with a universal C (depending on Lie algebra normalization).
For fixed physical perimeter ell at UV spacing a0,
  m≈ell/a0,
  β_W(a0)≈c log(1/a0),
so (240/β_W)*C*m ≈ C'/(a0 log(1/a0)),
which DIVERGES. This does not prove the actual variance large:
it proves that applying the cited variance estimate with
the **raw bare-link gradient** does not establish sourcewise
fine-field approximation.

Potential remedy, not yet proved: use a dense family of
positively-time-supported flowed or smeared gauge-invariant
observables for which the fibre gradients have cutoff-uniform
bounds, and prove the one-sided conditional variance, chart
mass and OS dictionary for their actual Wilson regularization.

Exact independent-iid SU2 diagnostic:
if U_1,...,U_m are independent with class law proportional
to exp(β Re tr U/2), then
  E[(1/2)tr(U_1...U_m)]
    = [I_2(β)/I_1(β)]^m.
For a=2^-n, β=n, m=2^n,
  n  beta m       log10 expectation
  4   4   16       -2.91
  8   8   256      -22.17
  12  12  4096     -231.75
  16  16  65536    -2752.69.
Even though each link becomes concentrated near identity,
long products Haarize due independent multiplicative
fluctuations. This is a toy and **not the true
plaquette-correlated 4D Wilson measure**, nor evidence of a
mass gap. It illustrates why raw-path approximation is costly.

## 6. NEW exact rank-count obstruction for any subextensive coarse projector in a massless reference theory

Let spatial lattice be the 3-torus Z_L³, with free massless
nonzero one-particle modes of frequency
  ω_L(n)=2 [∑_(i=1)^3 sin²(π n_i/L)]^{1/2}.
Take T_L=exp(-t ω_L), diagonal on the momentum basis,
and N_L(E)=#{n≠0:ω_L(n)<=E}.

For ANY orthogonal coarse projection P_L with
  rank(P_L)<N_L(E),
linear algebra yields a nonzero unit vector in
  ran 1_[0,E](H_L) ∩ ker P_L.
For that vector y,
  <y,T_L y> >=exp(-t E)||y||²,
so with Q_L=I-P_L,
  ||Q_L T_L Q_L||>=exp(-t E).                 (65.5)

At each fixed E>0, N_L(E)~c_E L³. Thus if
  rank(P_L)=o(L³)
as L->infinity, for EVERY E>0 eventually
rank P_L<N_L(E), and
  ||Q_L T_L Q_L|| ->1.
This rigorously rules out volume-uniform q_f<1 in a
gapless massless reference theory after removing only
a subextensive number of coarse modes.

Independent exact discrete Fourier counts at E=0.6:
  L 16:18, 32:122, 48:436, 64:972, 96:3334, 128:7856.
Counts are for one scalar mode/p, without assuming physical
SU2 transverse/gauge degeneracies.

This result is an operator-theoretic *method obstruction*,
NOT a theorem about the actual Yang–Mills spectrum.
True RG coarse **fields at all spatial blocks** can span
an extensive subspace, so the no-go does NOT rule out
physically appropriate block projections. It warns against
mistaking a finite hand-picked Wilson-root family for
a complete coarse IR field sector.

## 7. Formal critical RED and target decision

For ORIGINAL I7 and all cutoff sectors:
  exact positive OS T_k at time 2a_*(k),
  true nonvacuum P_k,
  either
    (i) q_c+q_f<1,
  or
    (ii) q_c,q_f<1 and
         ||P_k T_k (I-P_k)||²
                  <(1-q_c)(1-q_f)
with a cutoff/volume-independent strict margin.
Neither model-specific estimate has been proved.

For the ALTERNATIVE continuum-only B14:
  exact same-Wilson positive-time coarse algebra B_(+,k),
  proper OS projection P_k onto its image,
  uniform q_c<1 on that coarse subspace,
  sourcewise one-sided fibre conditional variance ->0 for
  a dense physical regularized test family,
  same-net OS Gram convergence and fixed physical time.
The abstract paper implication to continuum gap is closed,
but each identified true model producer remains OPEN.
This is not a substitute for the exact original I7 theorem.

One more concrete route (preprint Prop148/Cor149):
  sup_j∑_(e≠j) sup_V |Cov_(ζ_V)(force_e,force_j)|
   < 2/π²,
plus the uniform weighted/far-tail bound, with the exact
true conditioned Wilson fibre law and all volumes/exhaustions.
The existing old/new-R activities do not prove it.

**No new Lean verification** was initiated because true
physical SU2 I7 paper closure has not been achieved.
The previously accepted Round55--63 statements remain intact.
No unconditional Clay Yang--Mills mass gap claim is made.
