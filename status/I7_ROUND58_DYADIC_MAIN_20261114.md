# 第58轮 I7 最短主链：稀疏二进物理时间谱判据
Date: 2026-11-14
Branch: ym-i7-dyadic-time-20261114
Acceptance: **original 39/39 CONDITIONAL preserved; physical I7 OPEN**.

## A. Main theorem — sparsity of times without loss of spectral contraction

For each physical cutoff/volume regulator k let H_k be the genuine Osterwalder–Seiler gauge-invariant Hilbert space, Omega_k the vacuum, and T_k = exp(-tau_k H_k) its **positive** two-step or terminal-scale selfadjoint contraction. For the original v133 manuscript tau_k=2 a_*(k), a_*(k)=L^{K_*(k)} a_0 and 0<c_- Lambda_YM^{-1}<=a_*(k)<=c_+ Lambda_YM^{-1}.

For each centered **positive-time single based Wilson loop** gamma define v_(k,gamma) and its true reflected diagonal OS temporal moment
 M_(k,gamma)(n) = <v_(k,gamma), T_k^n v_(k,gamma)>_OS
 = E_k[conj(Theta F_gamma)*(translate_(n tau_k) F_gamma)].
The second identity needs the genuine infinite-time Wilson measure and the exact OS reflection/source dictionary, not a periodic wrap or a surrogate polymer measure. The family of all such single based loops must have dense linear span in the physical vacuum-orthogonal space; this uses the SU2 Mandelstam identity, finite-graph trace-orbit separation, Stone-Weierstrass, and the actual OS completion.

**Sparser physical RED58** (still UNPROVED in actual 4D SU2):
 there exists a common q in (0,1) such that for every k,gamma there
 is a finite C_(k,gamma) with
 M_(k,gamma)(2^j) <= C_(k,gamma)*q^(2^j)  for ALL j in Nat.

Then the spectral measure E_k of T_k gives, for q+epsilon<=1,
 (q+epsilon)^(2^j) ||E_k([q+epsilon,1]) v_(k,gamma)||^2
    <= C_(k,gamma) q^(2^j).
Sending j->infinity proves E_k([q+epsilon,1]) v_(k,gamma)=0.
**Do not make the incorrect inference that diagonal one-step bounds alone
extend by density**: the conclusion uses the spectral PROJECTOR killed
on a dense linear span, not simply the diagonal first-moment inequality.
Since every such projector is bounded, it vanishes on the entire physical
space, and letting epsilon down to zero gives
   0<=T_k|Omega_k^perp<=q*I
for every k. Thus the original I7 full finite-complex-Gram condition holds
with eta=1-q uniformly.

The scalar Jensen proof also implies the first-step bound for an individual
v, but only the all-j spectral-support argument can pass from the
single-loop dense family to arbitrary complex linear combinations.

## B. Strict Lean target (independent of physical input)

New source YMOriginal/OriginalI7_DyadicTemporalMoments.lean contains:
- dyadic_power_bound_forces_rate:
  if x^(2^j)<=C q^(2^j) for all j and q>0, then x<=q.
- dyadic_moment_decay_forces_one_step:
  under positive-reference moment m0 and explicit DYADIC Jensen plus
  the stated dyadic decay premise, m1<=q*m0.

Only scalar arithmetic is claimed. Actual hJensen requires a common
positive selfadjoint Wilson transfer; physical hDecay is still the RED.
The new CI gate must report Success and #print axioms only standard
[propext, Classical.choice, Quot.sound] before promotion.

## C. Further permission: subexponential word-dependent amplitudes

For a common physical mass m_*>0, it is enough to show at dyadic times
 M_(k,gamma)(2^j)
  <= C_(k,gamma) (1+2^j)^{p_(k,gamma)}
       exp(-m_* tau_k 2^j),
where both C_(k,gamma) and the finite nonnegative p_(k,gamma) may depend
on regulator and Wilson loop. Since
  log C + p log(1+n) = o(n)
for each fixed (k,gamma), taking 2^j-th roots in the spectral
measure inequality still yields
  sup supp spectralMeasure(T_k,v_(k,gamma))
   <= exp(-m_* tau_k).
Hence the same physical mass exponent m_* is retained: polynomial
prefactors do not reduce it, even if their exponent is not uniformly
bounded over k,gamma. This is a paper-level mathematical argument,
NOT a physical Wilson estimate nor a Lean-certified source.

More generally, any fixed-word subexponential multiplier A_(k,gamma)(n)
with limsup_(j->infty) log A_(k,gamma)(2^j)/2^j <= 0 is harmless.
The essential requirement is a COMMON POSITIVE exponent m_*.

At each cutoff:
 T_k <= exp(-m_* tau_k) I,
so H_k|Omega^perp >= m_* I under true spectral calculus.
For the original manuscript's uniform Gram q, use
 q := exp(-m_* tau_min) < 1,
 tau_min := 2 c_- / Lambda_YM >0;
then T_k<=qI for every regulator. Uniform physical generator gap in
fact has the sharper lower bound m_* when no physical-unit loss occurs.

## D. Specific unavoidable genuine model obstruction

The existing public YMOriginal/Original24_ConnectedRootDistance.lean and
YMConditional/Original33_ClusterTail.lean prove rooted connected-series
distance bounds only under their explicit hPenroseDistance, hFP,
hactualDistance, hweight, hcount, hLocalNorm inputs. They do not identify
the resulting R-sector series with the complete true Wilson/OS
reflected temporal covariance for every dyadic physical-time shift.
The terminal effective Gaussian / nonperturbative infrared sector and
a single positive rate uniform in all cutoffs are not produced.

One may try to construct, within the true physical Wilson measure,
 M_(k,gamma)(2^j)=M_IR(k,gamma,j)+R_UV(k,gamma,j)
with explicit equality, and then establish
 |M_IR| <= D_(k,gamma,j) exp(-m_IR tau_k 2^j),
 |R_UV| <= B_(k,gamma,j) exp(-m_UV tau_k 2^j),
for a common positive min(m_IR,m_UV), allowing only subexponential
word-dependent prefactor growth. Neither this exact physical
decomposition nor its IR bound is currently established by these Lean
certificates. In particular, a time-independent remainder floor
epsilon_(k,gamma) cannot close I7 as j->infinity.

For positive OS transfer, Jensen gives
  M(2n)*M(0) >= M(n)^2.
The direction is IMPORTANT: positive transfer alone does NOT
upper-bound the long-time correlation by powers of its one-step
correlation. No fictitious dyadic squaring bootstrap is permitted.

## E. Literature checkpoint

- Shen–Zhu–Zhu, CMP 400 (2023): published strong-coupling lattice
  exponential clustering, NOT 4D weak-bare-coupling continuum.
- Deep Bhattacharjee et al. 2026 Hexagon preprint version 7:
  one physical cube mixing estimate is only a CONDITION, not proved
  uniformly along the continuum tuning.
- Deep Bhattacharjee et al. 2026 Preprints.org preprint posted
  November 12, "The Yang–Mills Mass Gap from One Bound at One Scale":
  its own abstract explicitly says its one-scale partition-function
  bound is OPEN at weak coupling. Not a solution to our I7.
- Clay Mathematics Institute continues to list the problem as unsolved.

## F. Exact status

PAPER CLOSED: scalar sparse-times and polynomial-prefactor spectral lemma.
LEAN: pending official strict CI for the scalar source. No Lean claim about
actual full physical Yang–Mills.
ORIGINAL: 39/39 only CONDITIONAL, with named published and model inputs.
REMAINING RED: true fixed-physical-time SU2 Wilson OS-reflected sparse
diagonal autocorrelation with one cutoff- and word-uniform positive exponent.
I7: OPEN.
