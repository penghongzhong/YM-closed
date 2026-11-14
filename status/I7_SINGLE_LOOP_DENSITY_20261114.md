# Round 55 I7: SU(2) single-loop reduction

Date: 2026-11-14
State: I7 OPEN; algebra/density argument only, no model-side Yang--Mills mass-gap claim.

## 1. Exact Mandelstam trace identity

For A,B in SU(2), Cayley-Hamilton and det B=1 yield
B + B^(-1) = (tr B) I. Therefore

  tr(A) tr(B) = tr(AB) + tr(AB^(-1)).

With the project's Wilson root W(A)=2-Re tr A=2-tr A,

  W(A)W(B)=2W(A)+2W(B)-W(AB)-W(AB^(-1)).

Both composite holonomies come from actual single closed paths if A,B are loops based at the same spatial point. Thus products of arbitrary finite based Wilson roots reduce inductively to finite *linear combinations of individual* based Wilson roots. This is a classical identity, not a new theorem.

Sources: Loll, Nuclear Physics B (1992), DOI 10.1016/0550-3213(92)90200-U; Bratholdt and Cooper, Rend. Istit. Mat. Univ. Trieste (2001).

## 2. Finite connected spatial graph: standard density proof

For a connected finite graph Gamma=(V,E), with compact group SU(2) and local site gauge transformations, fix a spanning tree and base point x0. The gauge-orbit space is a compact quotient naturally identified with SU(2)^r/Ad(SU(2)), where r=|E|-|V|+1 (one group element per chord).

Known SU(2) character-variety theory: traces of all group words separate simultaneous conjugation orbits on SU(2)^r (Bratholdt-Cooper). Therefore the unital real algebra of based closed-loop traces separates points on the compact quotient. Stone-Weierstrass makes it uniformly dense in continuous gauge-invariant real functions. The trace fusion identity shows the *real linear span* of all single-loop traces is already an algebra, and the empty trace is the constant 2. Equivalently,

closure_span_R{1, W_gamma: gamma based closed loop} = C(X_Gamma,R).

For any finite regular Borel probability measure, the same family is dense in gauge-invariant L2. After centering, {W_gamma - E W_gamma} spans the mean-zero gauge-invariant L2 closure. The actual Osterwalder--Seiler Hilbert space / positive-time transfer identification, including cyclicity of time-zero cylinder observables, remains a separate model-specific interface, not a consequence of this finite-graph fact.

## 3. Exact fixed-physical-time criterion

For lattice spacing a_alpha tending to zero and a fixed tau>0 set
tau_alpha = 2 a_alpha ceil(tau/(2a_alpha)).
Then tau<=tau_alpha<tau+2a_alpha. Let T_alpha=exp(-tau_alpha H_alpha) on the actual vacuum-orthogonal physical space, with H_alpha>=0.

A sufficient dynamical theorem is the following:

Exists m_*>0 for every regulator alpha and every centered *single* based Wilson loop gamma there exists a finite C_(alpha,gamma) such that for ALL n in N,

  0 <= <v_(alpha,gamma),T_alpha^n v_(alpha,gamma)>
     <= C_(alpha,gamma) exp(-m_* n tau_alpha).

Assuming density in the actual physical Hilbert space, the spectral projection proof from Round 54 gives

  T_alpha|Omega_perp <= exp(-m_*tau_alpha)I
                       <= exp(-m_*tau)I.

Consequently all finite complex Gram forms satisfy
G0(F)-Gtau_alpha(F) >= (1-exp(-m_*tau)) G0(F).

Neither word- nor regulator-uniform amplitudes are necessary. The rate m_* MUST be uniform in both.

Reuse the existing Original16_FromI7.lean only with its time parameter a_effective=tau_alpha/2, which is NOT the microscopic lattice spacing a_alpha. The manuscript has to match this exact physical dictionary.

## 4. Noncircularity guardrails

- Original24 old/new-R convergent two-root remainder series is not the complete physical Wilson covariance. The full infrared effective Gaussian and bulk sectors have not been dominated.
- All genuine Wilson covariance/source dictionaries must be proved, including all arbitrarily large temporal separations, and have no time-independent error floor.
- Finite periodic temporal cylinders cannot support exponential decay for all n. Remove temporal wrap before applying the n -> infinity spectral argument.
- Per-word decay without a common rate fails: on l2(N), define T e_j=exp(-1/j)e_j. Every basis autocorrelation decays exponentially with a j-dependent rate, but sup spec T=1 and no gap exists.
- Established lattice strong-coupling theorems at small beta do not cover the large-beta asymptotically-free ultraviolet trajectory without additional RG control.
- Do not claim any increase of the historical 39/39 conditional environment count or physical I7 closure.

## 5. Single RED physical target

For the true infinite-time SU(2) Wilson/OS measure, prove uniformly in all regulators and all based spatial loop words:

  abs Cov_alpha(W_gamma,theta_(n*tau_alpha) W_gamma)
       <= C_(alpha,gamma) exp(-m_* n tau_alpha),

with fixed positive m_*, n>=0 and finite word-dependent prefactor.

The finite-graph density reduction and scalar spectral argument are complete on paper. This Wilson model inequality is NOT proved; I7 is OPEN.
