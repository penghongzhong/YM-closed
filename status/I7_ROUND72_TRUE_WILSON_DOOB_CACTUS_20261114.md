# 第72轮｜真正Wilson有限步传递、基态Doob、任意大小SU2仙人掌规范图统一gap，以及真实立方共享边反例

Date: 2026-11-14
Branch: ym-i7-round72-true-wilson-doob-cactus-20261114
Parent: ym-i7-round71-exact-os-memory-20261114

## 0. STATUS and acceptance scope

Original physical 4D SU(2) Yang–Mills I7 is OPEN.
The accepted historical 39/39 main environments remain only CONDITIONAL with an explicit I7 hypothesis.
The numerical/cactus results below are strictly paper-level results on exactly named real SU(2) Wilson temporal-convolution models. No new Lean declaration, no CI; per user, Lean begins only after the complete original I7 is closed on paper.
The full Clay mass-gap problem is not solved.

## 1. Exact gauge-invariant PURE temporal convolution spectrum (spatial graph girth lemma)

Let G=(V,E) be a finite connected spatial simple graph with girth ℓ>=3.
Each directed link carries SU(2), with normalized Haar measure,
and local gauge action U_e -> g_(source e) U_e g_(target e)^(-1).
Define the one-link Wilson heat kernel
  k_beta(U)=exp[β tr(U)/2]/Z_beta,
  Z_beta=∫exp[β tr(U)/2]dHaar(U)=2 I1(β)/β,
and K_beta convolution with this CENTRAL positive kernel.
SU2 Peter–Weyl gives one-edge nonnegative eigenvalues
  rho_j(β)=I_(2j+1)(β)/I1(β), j∈{0,1/2,1,...}.
rho_0=1, all 0<rho_j<1 for j>0,
and rho_j<=r_beta:=I2(β)/I1(β) for j>=1/2
(classical monotonicity of I_n(β), n>=1, at β>0).
Thus K_E=⊗_(e∈E)K_beta,e is a positive gauge-equivariant
Haar-stationary contraction.

A Peter–Weyl spin-network basis on L²(SU2^E)^gauge
labels each edge by j_e and vertices by invariant intertwiners.
At a vertex with precisely ONE incident nonzero j_e,
the invariant tensor space is {0}. Hence any nontrivial
spin network's occupied-edge support has no degree-one vertex.
Any finite nonempty graph with min occupied degree>=2 has a cycle,
hence support has >=ℓ nontrivial edges.
The K_E eigenvalue on that spin-network state is
  λ_spin =∏_(e∈E) rho_(j_e)(β) <=r_beta^ℓ.

A shortest simple cycle γ of length ℓ carries a legitimate
gauge-invariant fundamental Wilson trace
  W_γ(U)=tr(ordered product_(e∈γ) U_e^(±1)).
It has Haar mean0 and K_E W_γ=r_beta^ℓ W_γ.
Therefore the bound is attained:
  ||K_E|_(L²(gauge)⊖C1)||=r_beta^ℓ.     (72.1)

For the ordinary 3D cubic open-boundary lattice, ℓ=4.
For periodic cubic lattice with >=4 sites along EACH direction,
ℓ=4. IMPORTANT small-volume exceptions: period3
has noncontractible winding cycles of length3, period2
has doubled/parallel oriented links and winding 2-cycles;
the formula must use the actual graph's girth.
For ℓ=4,
  eta_kin(β)=1-[I2(β)/I1(β)]^4 >0
independently of spatial volume.
Numerical Bessel evaluations:
 β=1 q=0.003328485, η=0.996671515;
 β=2.3 q=0.052765965, η=0.947234035;
 β=4 q=0.187511695, η=0.812488305;
 β=8 q=0.450468627, η=0.549531373;
 β=16 q=0.679186622, η=0.320813378;
 β=32 q=0.826586925, η=0.173413075.
As β→infinity, r_beta=1−3/(2β)+O(β^-2),
 eta_kin(β)=6/β+O(β^-2).

**This is the exact UNDRESSED spatial-time-link transfer K, not
the full Wilson T=D K D. In the latter the true vacuum is not
the Haar constant state and D mixes Peter-Weyl spin networks.
No physical I7 margin is inferred from eta_kin.**

## 2. Exact full true finite-spatial-volume Wilson Doob transform

Let E denote all spatial links and let D(U)>0 be the
symmetric positive half-spatial-plaquette multiplication
  D(U)=exp[(β/4)Σ_(spatial p) tr U_p].
Let K=⊗_e K_beta,e and let T=D K D, acting on the
full kinematic L²(SU2^E), or after exact gauge projection
onto the invariant physical subspace. On a fixed finite
graph and β>0, the full integral kernel
  T(U,V)=D(U)K(U,V)D(V)>0
is continuous, symmetric, positive-definite, compact
(trace class) and positivity-improving.
Therefore there exists a unique positive normalized
top eigenfunction ψ, top eigenvalue λ0>0;
ψ is gauge invariant because the full operator
commutes with all local gauge transformations.
The normalized physical Wilson transfer is T/λ0.

Write w=Dψ. The eigenfunction equation is
  λ0 ψ(U)=D(U)(K w)(U),
and λ0=∫w(U)(Kw)(U) dHaar(U).
The exact ground-state (Doob) Markov transition is
  (P f)(U)=(K(w f))(U)/(Kw)(U).                 (72.3)
Its stationary law is
  π(dU)=ψ(U)^2 dHaar(U)
       =w(U)(Kw)(U)/λ0 dHaar(U).
The stationary two-time flux is
  J(dU,dV)=w(U)K(U,V)w(V)/λ0 dUdV,
symmetric, nonnegative, with both marginals π.
The Dirichlet form of the EXACT physical transfer is
  E_P(f)=<f,(I−P)f>_π
    =[1/(2λ0)]∫∫ K(U,V)w(U)w(V)
             |f(U)−f(V)|² dUdV.             (72.4)

All f are gauge-invariant if we seek original physical
I7. This identity neither assumes an effective
KS Hamiltonian nor drops microscopic return paths.
For the original positive integer physical-time
step n_*(a0), the exact Markov operator is P^(n_*),
stationary π and two-time flux J_(n_*)=π P^(n_*).
A strictly positive physical-space spectral gap
at this true fixed physical time is the
full-Poincare statement
  Var_π f <=eta_*^(-1) E_(P^(n_*))(f)
for ALL gauge-invariant f and all regulators,
with eta_* uniform in cutoff,volume,exhaustion.

### Cheeger/capacity target is an equivalent strong geometric producer

For the actual terminal time define
  Φ_* = inf_(gauge-invariant A,0<π(A)<=1/2)
           J_(n_*)(A,A^c)/π(A).
By the classical reversible-Markov Cheeger inequality,
  gap(I−P^(n_*)) >= Φ_*²/2.
Thus a cutoff/volume-uniform lower bound Φ_*>=φ0>0
would close I7 with eta_*=φ0²/2.
But proving it is a FULL physical nonperturbative
problem. This identity alone does not improve the
genuine H2 infrared control, and does not follow
from original old/new-R polymer activity bounds.
The stationary π=ψ² here is the true infinite-time
vacuum slice state; it is NOT automatically the
single-slice marginal of a finite-periodic-time
Euclidean Gibbs measure.

## 3. New strict general single-block Doeblin lemma, independent of magnetic D oscillation

Let (X,μ) be any compact probability space, K a symmetric
strictly positive Markov kernel with a density satisfying
  0<m<=K(x,y)<=M<infinity,  0<=K<=I.
Let D(x)>0 be arbitrary continuous bounded multiplication
and T=D K D. Let ψ>0 be the normalized simple top
eigenfunction, λ top eigenvalue, and w=Dψ.
As in §2,
  π(x)=w(x)Kw(x)/λ,
  P(x,dy)=K(x,y)w(y)/(Kw)(x) μ(dy).
Let W=∫w dμ. Then
  mW <= (Kw)(x) <= MW,
  mW² <=λ<= MW².
Hence the ratio of the Markov kernel to its
ACTUAL invariant measure satisfies, for ALL x,y,
  P(x,dy)/π(dy)
   = λ K(x,y)/[(Kw)(x)(Kw)(y)]
   >=(m/M)² =:eps.                         (72.6a)

This is a global one-BLOCK minorization
  P(x,dy)>=eps π(dy)
with epsilon>0 independent of the oscillation
or magnitude of D. Therefore, on π-mean-zero f,
  <f,P f>_π <=(1−eps)||f||²_π,
and since P is positive selfadjoint
  ||P|L²_0(π)|| <=1−eps.
This is rigorous with no small-magnetic-field
assumption. It is a one-block statement; attempting
to use the full spatial model global min/max
m/M would lose the bound exponentially in volume.

For SU2, the original k_beta(U)=exp(βcosθ)/Zβ
has max/min ratio exactly e^(2β).
Every convolution power k_beta^{*n} remains
between the same MIN and MAX of k_beta,
because convolving with a probability kernel
preserves these pointwise bounds.
Thus, for n=4,
  min k_beta^{*4}/max k_beta^{*4} >=e^(−2β).
Take K=K_beta^4 on a full SU2 plaquette
holonomy and D=d_beta(U)=exp[(β/4)tr U].
Then the exact one-loop finite-Wilson transfer
  t_beta=d_beta K_beta^4 d_beta
has
  ||(t_beta/λ_beta)|ψ_beta^perp||
      <=1−e^(−4β).                          (72.6)

The constant is crude but fully explicit:
 beta=0.5 eta>=0.1353353,
 1 eta>=0.01831564,
 2.3 eta>=1.010394e−4,
 4 eta>=1.125352e−7,
 8 eta>=1.266417e−14.
It is positive for fixed beta but tends to ZERO
when beta→infinity; this does not establish
a cutoff-uniform continuum physical mass gap.

## 4. NEW significant model-specific theorem: arbitrary-size actual Wilson transfer on SU2 cactus spatial graphs

Let a finite connected spatial graph be a TREE of
edge-disjoint, four-edge plaquette cycles, with bridges
only between plaquette basepoints. Every bridge link
belongs to NO spatial plaquette and every spatial
plaquette consists only of its OWN four loop edges.
On the graph×temporal-line pure SU2 Wilson theory,
the exact one-slice transfer is T=D K D as in §2.
This is the finite-time WILSON transfer, not an
artificial KS Hamiltonian nor a continuum-time limit.

Choose the spanning tree containing three of the
four edges of each plaquette and all bridges.
After exact gauge quotient, the kinematic physical
Hilbert becomes
  H_phys ~= L²(SU2^{V_tree})^{Ad_diag(root)},
retaining the complete boundary relative orientation
sectors shown essential in Round69.

Each one of the four temporal link convolution
factors around a loop, when expressed in its
root-transported holonomy U_z, acts as a
CENTRAL group convolution K_beta on U_z.
They commute, so the four yield K_beta^4.
Each bridge e acts on all DESCENDANT holonomies
by simultaneous conjugation, and the corresponding
temporal link convolution becomes the group twirl
  (B_e f)({U_z})
    =∫ k_beta(g) f({g U_z g^(−1):z∈Desc(e)},
                      {U_z:z∉Desc(e)}) dg.
Every B_e is positive selfadjoint and 0<=B_e<=I:
the SU2 central kernel has all Peter-Weyl
coefficients rho_j>=0. On a rooted tree,
descendant sets for two distinct bridges
are either disjoint or nested; centrality
of k_beta implies all bridge twirls commute.
The central single-loop kinetic K_beta^4
commutes with every bridge twirl.

The half-spatial magnetic weight FACTORIZES as
  D({U_z})=∏_z d_beta(U_z),
  d_beta(U)=exp[(β/4)tr U].
Each d_beta is a CLASS function, so its
multiplication commutes with every bridge
simultaneous-conjugation twirl.

Therefore the exact transferred Wilson operator
on the full loop-coordinate Hilbert is
  T_cactus=(⊗_z t_beta,z) * (∏_(bridges e) B_e),
where t_beta,z=d_beta K_beta^4 d_beta,
and every factor in the product commutes
with all other factors. Gauge root projection
may be applied before or after.

Let ψ_beta be the unique top eigenfunction of t_beta,
which is class-invariant by simple Perron and
conjugation symmetry, and let λ_beta be its top
eigenvalue. Define
  Ψ=⊗_z ψ_beta(U_z).
Ψ is fixed by all B_e, hence it is the exact
positive physical vacuum of T_cactus, with
top eigenvalue λ_beta^{N_loop}.

After λ_beta^{−N_loop} normalization, the
tensor transfer ⊗ (t_beta/λ_beta) has vacuum
Ψ and exact nonvacuum norm <=1−e^(−4β)
from the single-block Doeblin lemma §3.
Every bridge factor B_e is an operator
between 0 and I that commutes with the
tensor transfer and fixes Ψ. Therefore
  0<=T_cactus/λ_beta^{N_loop}
     <=⊗_z(t_beta/λ_beta),
and taking the vacuum-orthogonal restriction:
  ||T_cactus/λ_beta^{N_loop}|Ψ^perp||
       <=1−e^(−4β),                    (72.7)
independent of the number of loops, the
number of bridges, the finite spatial volume,
and the rooted tree shape.

This is a genuine finite-step pure SU2 Wilson
transfer theorem on the EXACT specified
spatial cactus graph, unlike the previous
KS graph-Hamiltonian result. It uses the
real gauge-projected OS transfer and all
mixed Wilson loop roots of that graph;
it is a true paper-level partial physical
lattice gauge result, but NOT a claim about
3D cubic spatial graph / 4D continuum I7.
For fixed beta its physical excitation gap
in lattice-time units is at least
  −log(1−e^(−4β))>0.

Why it does NOT close original I7:
  (1) the cactus graph has no 3D cubic spatial
      cells/face-sharing plaquettes;
  (2) when real face links are shared,
      magnetic D no longer factorizes into
      one-group class factors under the
      independent-loop changes induced by
      temporal K_e, and bridges are no longer
      conjugation-only twirls commuting with D;
  (3) beta=beta(a0) grows along asymptotic
      freedom, and the explicit lower bound
      e^(−4 beta(a0)) tends to0; no uniform
      PHYSICAL fixed-clock contraction has
      been proved by this argument;
  (4) real RG terminal effective time kernels
      are not proved to preserve this special
      product/twirl representation.

## 5. NEW exact REAL adjacent-face obstruction, quantified at a flat configuration

Consider a genuine local 3D cubic lattice edge e.
An interior spatial edge belongs to FOUR
spatial plaquettes. Fix all other spatial
links equal to I and vary ONLY e with
group value U, so each of its four
incident spatial plaquette holonomies
is U or U^{-1}. SU2 trace is inversion
invariant.

The local half-magnetic Wilson factor
associated with those four faces is
  D_e(U)=exp[(β/4)*4 tr U]
         =exp[2β cos θ],
  U has tr U/2=cos θ.
At flat U=I, D_e(I)=exp(2β).

Now apply the ACTUAL one-link temporal
Wilson convolution K_beta to this
local factor while fixing all other links.
By exact SU2 Haar integration,
  (K_beta D_e)(I)
    = [1/Z_beta]∫ exp(β cosθ)
                     exp(2β cosθ)dH(U)
    = Z_(3β)/Z_beta.

Define the relative noncommutation defect
  R_4(β)= (K_beta D_e)(I)/D_e(I)
        = e^(−2β) Z_(3β)/Z_beta
        = e^(−2β) I1(3β)/(3 I1(β)).
For β>0, R_4(β)<1 strictly.
The weak bare-coupling asymptotic is
  Z_beta~Const exp(β) beta^(−3/2),
hence
  lim_(β→infinity) R_4(β)=3^(−3/2)
    =0.19245008972987526...
and
  lim_(β→infinity)[1−R_4(β)]
     =1−3^(−3/2)≈0.80754991027>0.   (72.8)

Numerical exact modified-Bessel check:
 beta    R_4(beta)
 0.5    0.466773777
 1.0    0.315563337
 2.3    0.226929011
 4.0    0.207857857
 8.0    0.199151756
 16     0.195616293
 32     0.193992042.

For only TWO adjacent plaquettes sharing e,
replace 2β by β in D_e and 3β by2β:
  R_2(β)=e^(−β)Z_(2β)/Z_beta
         =e^(−β)I1(2β)/(2 I1β)
       ->2^(−3/2)=0.35355339059...
This is the first shared-edge motif that breaks
the cactus commuting-bridge factorization.

The exact commutator witness is
  [K_e,M_(D_e)] 1 (U=I)
    =(K_e D_e)(I)−D_e(I)≠0,
while on a cactus BRIDGE edge e belongs to
no spatial face, so D is independent of
that bridge link and [K_e,M_D]=0.

**Interpretation:** even at the FLAT
configuration and in the β→infinity
weak bare-coupling regime, simply treating
shared spatial plaquette edges as harmless
tree-bridge updates incurs a RELATIVE
order-one error. This is a genuine local
SU2 Wilson integral; it is NOT itself a
lower bound on the physical mass gap or
a proof that a different nonperturbative
renormalized comparison is impossible.
The correct 3D cubic source/temporal
kernel must keep these shared-edge effects
fully nonperturbatively, not absorb them
in an asserted o(1) old/new-R activity.

## 6. Relation to existing original project verified statements

Existing Lean conditional main ledger 39/39 stays intact.
Original55 strict Mandelstam identities already
permit the exact mixed Wilson roots and gauge
trace products. The SU2 role of spatial girth,
actual time-link character K, Doob h-transform
and new cactus factorization are PAPER results
this round, not new Lean claims.

Original24_BalabanTwoRootRealFullSeries.lean
bounds named old/new R activity insertions but
does NOT prove:
  (a) the true 3D cubic spatial magnetic
      shared-edge temporal transfer has
      a uniform-volume positive conductance,
  (b) the true terminal ground state ψ
      has a cutoff/volume uniform local tilt
      or gives the required π conductance,
  (c) the full same-physical-time B08 source
      and OS spectral dictionary matches a
      stable terminal reference as above.
The exact Doob flux is an alternative
target to Feshbach Sigma(1):
  π(U)P(U,V)=w(U)K(U,V)w(V)/λ0.
Either method still needs true H2 infrared
nonperturbative dynamics for the cubic graph.

## 7. Closure tree, only load-bearing nodes

4D SU2 original I7
├─ GREEN historical 39/39 CONDITIONAL
├─ GREEN exact gauge-invariant kinetic spectrum
│        ||K|physical⊖1||=rho_half(beta)^girth
├─ GREEN full finite Wilson h-transform,
│        exact invariant ground-slice π and
│        stationary two-time Dirichlet flux
├─ GREEN one-compact-block universal Doeblin:
│        gap >=(inf k/sup k)^2
├─ GREEN arbitrary-size SU2 Wilson cactus
│        with true finite-step transfer:
│        nonvacuum ||T||<=1−exp(−4beta)
│        uniform in loop/block count
├─ GREEN true cubic shared-edge flat-group
│        defect R4(beta)->3^(−3/2)≠1
├─ YELLOW original same-Wilson ground-state
│        source/OS/B08 physical-time dictionary
├─ RED cubic face-sharing links defeat
│       the commuting bridge/tensor decomposition;
│       no uniform true nonperturbative
│       π-Poincare/flow conductance established
├─ then actual I7 physical q_IR<1
├─ then original U-I-C master theorem
└─ I7 PAPER OPEN; no Lean per user policy.

## 8. Sources

- M. Lüscher, "Construction of a Selfadjoint, Strictly Positive Transfer Matrix
  for Euclidean Lattice Gauge Theories",
  Comm.Math.Phys.54 (1977) 283–292,
  DOI 10.1007/BF01614090.
- K. Osterwalder and E. Seiler,
  "Gauge Field Theories on a Lattice",
  Ann.Phys.110 (1978) 440–471,
  DOI 10.1016/0003-4916(78)90039-8.
- Peter–Weyl spin network graph representations
  (existing published group representation material);
  exact edge Casimir and gauge group action discussed in
  Kogut–Susskind lattice SU2 Hamiltonian references.
- Reversible Markov Cheeger lower bound:
  gap(I−P)≥Phi²/2, see standard
  Markov-chain spectral theory.
- The unproved weak-coupling-to-IR conditional
  dynamics remains OPEN; neither new theorem
  challenges the Clay official problem status.
