# 第60轮｜I7 真正非微扰红外接口：严格反向审计
Date: 2026-11-14
Research branch: ym-i7-real-ir-audit-20261114
Base: ym-i7-b14-vanishing-error-20261114 @ 387983f8348250502935f616bdb0541928836c30

## 0. Acceptance boundary

- Physical I7: **OPEN**. Original 39/39 are conditional, NOT model-level Clay closure.
- Round 59 continuum-only asymptotic B14 + same-Schwinger bookend were strictly Lean-compiled, but all model-specific physical Gram inputs remain assumptions.
- **No additional Lean theorem is proposed merely for a higher verification count in this round.** This is a mathematical/red-point audit.
- New external reference: Aleksandar Mihajlovic, *SU(2) Yang–Mills: Spectral Bounds, Vacuum Concentration, and Criteria for the Continuum Limit*, arXiv:2611.11534v1 (8 November 2026), Sections 35, 43, 57. It is a preprint and explicitly does **not** prove a uniform 4D continuum gap.

## 1. Exact original24 root constant: hidden dependence on physical contour size

In the actually compiled source YMOriginal/Original24_DoubleFugacityFPTerminal.lean,
theorem original24_two_root_tree_O_aAct_from_U1_and_FP explicitly chooses

delta = kappa - cGeo*mu > 0,
B = (2*chi+1)^4,
E = exp(kappa * rootQ.card),
M = exp(rootP.card * delta/2) - 1,
C = M * 32*B^2*E/delta^2.

Thus the last rooted sum bound is <= C*aAct, where C is **not independently declared cutoff-uniform**. In the specialization
YMOriginal/Original24_BalabanTwoRootRealFullSeries.lean
the conclusion produces existential C_old and C_new, not fixed
cutoff/volume-independent numerical constants.

For a simple loop of fixed nonzero physical perimeter ell represented on bare links of spacing a0, its raw path length is of order ell/a0, and a self-avoiding path's root support cardinal has the same order. Consequently the EXPLICIT certified upper bound can behave as

C(a0) ~ exp(c/a0)

for positive kappa,delta; a merely logarithmic vanishing g(a0)^p of the U1 activity factor does NOT make C(a0)*aAct small or uniform. This establishes a failure of the EXISTING UPPER-BOUND CERTIFICATE, not a lower bound on actual correlations or a physical counterexample.

This issue can disappear if the roots are truly measured on terminal RG blocks of fixed physical size; however the exact source/jet dictionary transporting the genuine microscopic Wilson loop to a **uniform-complexity terminal source** is not proved by the displayed theorem. It cannot be asserted solely from the choice of a_*.

Additionally the final two-root Mayer bound controls O(C*aAct) ABSOLUTE SUMMABILITY and does not contain an explicit exp(-m*distance(rootP,rootQ)) factor. The separate
YMOriginal/Original24_ConnectedRootDistance.lean establishes distance decay under hPenroseDistance and hFP, but no model-level equality identifying the relevant complete physical Wilson OS covariance with the distance-controlled rooted sum is supplied. Therefore even the asserted UV-part temporal decay is not yet an unconditional physical statement.

## 2. The source-matched full physical covariance, before any RG approximation

Let mu_a be the actual reflection-positive Wilson measure, and let
F be a bounded centered gauge-invariant positive-time Wilson observable.
For a physical time t (on the allowed even time lattice), set

X = Theta F,     Y_t = tau_t F,

where Theta denotes linear time reflection; complex conjugation is
placed explicitly in the pairing. For small complex s,u, define

Z_{a,t}(s,u) = E_{mu_a}[ exp(s*conj(X) + u*Y_t) ],
Gamma_{a,t}(s,u) = log Z_{a,t}(s,u),

using the unique local branch with Gamma(0,0)=0. For finite bare Wilson
loops the observables are bounded and Z(0,0)=1, so the local derivatives
exist with no extra dynamical assumption. Direct differentiation yields

M_a(F;t) =
  E[conj(X)*Y_t] - E[conj(X)]*E[Y_t]
  = partial_s partial_u Gamma_{a,t}(0,0).

The OS norm uses t=0 and the *same reflection convention*, and the
shifted Gram uses the same F, geometry and state.

This identity is an exact noncircular *full Wilson* source-Hessian
interface. Any claimed RG decomposition must act on the TRUE
Gamma_{a,t}, including the terminal IR effective action, not merely
on the amplitudes named oldR/newR. The mixed derivative of a
truncated Mayer remainder is only part of this Hessian.

## 3. Coarse Euclidean conditional expectation is NOT automatically an OS projection

The strict Lean Round59 theorem exact_coarse_fine_inner is a Hilbert
orthogonal projection identity, which applies directly to Euclidean
L2 conditional expectation. This is legitimate as a law of total
Euclidean covariance, but it does NOT automatically supply a
projection on the physical OS quotient Hilbert space.

Explicit reflection-positive two-time counterexample:
Let x_-,x_+ be +/-1 with
  p(x_-=t,x_+=s)=(1+r*s*t)/4, 0<r<1.
The reflection swaps x_- and x_+. For any positive-time function f,
  E[conj(f(x_-))*f(x_+)]
     = |(f(+)+f(-))/2|^2 + r |(f(+)-f(-))/2|^2 >=0.
The centered vector f(s)=s has OS norm squared r>0.

Take the reflection-invariant coarse variable B=x_-+x_+. Then
  P_B f = E[x_+|B]=(x_-+x_+)/2,
which depends on NEGATIVE time and cannot be represented as a
function of x_+ only. Therefore even a reflection-equivariant
Euclidean conditional expectation need not preserve the positive-time
algebra. In particular, one cannot identify P_B with an OS Hilbert
orthogonal projection, or claim the two Euclidean covariance
components each form a positive transfer semigroup, without an
additional positivity/OS-null-space-preserving RG dictionary.

Safer replacement: on the ALREADY CONSTRUCTED physical OS Hilbert
space, define P_OS as the actual orthogonal projection onto the
closed span of an explicitly identified coarse observable sector.
This is a legitimate Hilbert projection, though its identification
with Euclidean RG integration is a SEPARATE physical problem.

## 4. A sharp non-circular block-operator gap budget (paper theorem)

Let T be a positive selfadjoint contraction on the OS vacuum-orthogonal
space; let P be an ACTUAL orthogonal projection there, Q=I-P. Suppose

  <x,Tx> <= q_c ||x||^2      (x in ran P),
  <y,Ty> <= q_f ||y||^2      (y in ran Q),
  ||P T Q|| <= eps,

with 0<=q_c,q_f<1 and eps>=0. For z=x+y,

  <z,Tz> <= q_c||x||^2 + 2 eps ||x|| ||y|| + q_f||y||^2.

The maximal eigenvalue of the 2x2 real symmetric coefficient matrix
is exactly

q_eff = (q_c+q_f+sqrt((q_c-q_f)^2+4 eps^2))/2.

Thus
  T <= q_eff I,
and a genuine strict full-sector contraction follows when

  eps^2 < (1-q_c)(1-q_f).

This is elementary Schur/min-max algebra, not an asserted YM estimate.
It permits the UV/IR off-diagonal term to be nonzero and does not
require P to commute with T. It also cleanly exposes the actual model
obligations: **coarse IR q_c<1**, fine UV q_f<1, and physical OS cross
norm eps below the geometric threshold. Old/new-R pointwise
polymer amplitudes are not by themselves a bound on ||P T Q||.

The 2026 Mihajlovic preprint Section 57 independently discusses the
full-Hilbert blocked-transfer error budget and explicitly leaves
its weak-coupling SU(2) verification open. Do not claim novelty or
that the paper establishes this physical criterion.

## 5. Finite-torus center sectors: local-loop density needs a precise scope

On a periodic 3-dimensional spatial lattice, define Z_alpha by
multiplying all SU(2) links crossing a fixed spatial alpha-plane
by the central element -I. For an elementary plaquette, intersections
with this plane are even, so its Wilson action is invariant.
Three commuting Z2 transformations label eight orthogonal sectors
H_chi, chi in {0,1}^3. A closed Wilson loop with winding parity
w_alpha transforms by (-1)^{w_alpha}. Every contractible local loop
is center neutral. If the physical vacuum is center neutral, then
the algebra of ONLY contractible Wilson loops applied to the vacuum
stays in H_0, and cannot be dense in the COMPLETE finite-torus
gauge-invariant vacuum complement.

This exact argument is written in Mihajlovic, arXiv:2611.11534v1,
Section 43 Theorem 43.1. It is a paper-level finite-volume statement,
not a theorem in the original YMUIC Lean repository.

Implication for our routes:
- Original16 and Original42 demand the whole finite lattice
  vacuum complement. Their hdense premise cannot be justified from
  the CONTRACTIBLE local Wilson family alone. To target their
  strong per-cutoff conclusion, noncontractible winding sectors must
  be included or treated by a separate sector analysis.
- The alternative continuum-only local OS/Wightman vacuum
  representation can instead be constructed cyclically from the
  genuine LOCAL Schwinger algebra, but must be identified with the
  physical Yang--Mills theory and retain nontriviality. It does not
  automatically control every finite-torus nonlocal charged sector.
- The Round55 claim of density of ALL based Wilson loops on a
  finite connected graph is consistent with this warning: ALL
  loops includes noncontractible cycles. Only a restricted
  contractible family fails to be dense in the full torus H.

## 6. Uniform physical-time alignment without assuming a_* converges

Let a0,k ->0, n_*(k) in N, a_*(k)=n_*(k)*a0,k,
0<a_*(k)<=c_+/Lambda_YM. Define a single macroscopic target
  t0=2*c_+/Lambda_YM>0,
and the even microscopic transfer exponent
  N_k=ceil(t0/(2*a0,k)).
Then N_k>=n_*(k) and the actual discrete even-transfer time
  t_k=2*a0,k*N_k satisfies t0<=t_k<t0+2*a0,k ->t0.
For a positive selfadjoint contraction S_k (the two-step
lattice transfer), spectral calculus gives
  0<=S_k^{N_k}<=S_k^{n_*(k)}.
So any terminal q-contraction implies the same q at the
single limiting physical time t0, without needing a_*(k)
itself to converge. This does NOT manufacture terminal q.
The B14 same-net source/time matching at t_k remains necessary.

## 7. Quantitative obstruction in an available vacuum-projection certificate

Mihajlovic Section 35 derives a local conditional Poincare seed
  gamma_B=(3/4) R(g)^{-2|B|},
  R(g)=(5/3) exp(256/g^4),
under its precise actual ground-state measure nu=h^2*d(Haar).
Thus
  gamma_B=(3/4)(3/5)^{2|B|} exp(-512|B|/g^4).

For a symbolic continuum trajectory g(a)^2~c/log(1/a),
the SEED itself tends to zero faster than every a^p:
  log gamma_B ~ -(512|B|/c^2)log(1/a)^2.
Even multiplying by the physical kinetic prefactor g^2/a
does not rescue this lower-bound CERTIFICATE; the resulting
guaranteed gap lower bound tends to 0. This does NOT show the
physical mass gap vanishes. It rules out promoting that
particular crude one-link density-ratio seed to a uniform
continuum I7 without much sharper estimates.

Crucially this Section 35 physical vacuum measure nu=h^2dHaar
must not be replaced by the four-dimensional Euclidean Wilson
conditional Gibbs law in a Hamiltonian Poincare estimate.

## 8. Exact next physical RED, with minimal dependencies

Use the already strict-pass asymptotic B14 / same-Schwinger
continuum-only theorem (CI 43552682497) as terminal logical bridge.

For every fixed finite family of true PHYSICAL, renormalized,
positive-time Wilson test vectors, choose a common q in (0,1).
Prove for the full genuine Wilson/OS source Hessians, at
t_k->fixed t0 and along the SAME joint cutoff-volume net,

  Q_t(k,s,c) <= q Q_0(k,s,c)
                  + A(s,c)rho^N + C_N(s,c) xi(k),

where N is a fixed history cutoff, 0<=rho<1, xi(k)->0,
and A,C_N may depend on s,c and N as in Round59.

To PRODUCE this, two operator/source estimates are essential:
  (IR) a strictly positive margin for the COMPLETE
       nonperturbative terminal effective Wilson sector,
  (UV) an actual source-matched residual bound that
       vanishes at fixed history cut, with physical
       time/source normalization and all IR sectors included.
The independent RG/OS density/representation identifications
remain explicit prerequisite dictionaries.

The old/new-R original24 theorem does NOT itself establish IR,
UV full source matching, rooted temporal separation, or
physical OS projection compatibility.

NO new physical I7 proof is obtained in this audit.
Do not add arbitrary Lean lemmas to inflate the 39 environments.

## 9. Frozen status

- Original conditional 39/39 unchanged.
- The 16 strictly compiled auxiliary Round55--59 statements
  remain preserved, with no new theorem count this round.
- Original physical I7: OPEN.
- New full physical terminal IR q: OPEN.
- Full actual Wilson source Hessian/RG identity and
  same-model OS-reconstruction dictionary: OPEN.
- Unconditional 4D SU(2) Yang--Mills mass gap: OPEN.
