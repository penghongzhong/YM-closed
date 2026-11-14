# I7: fixed-physical-clock and diagonal Wilson-word reduction (2026-11-14)

Status: **I7 remains OPEN.** This note contains two ordinary mathematical arguments, not a compiled Lean certificate or a physical SU(2) YM mass-gap proof. Historical 39/39 is CONDITIONAL (I7 and named published/model inputs are premises). Parent commit: 94ad767b8b885b7b6e5a9c5f632e329e2ec2ef42.

## 1. A necessary clock correction

Let \(\alpha\) label UV regulators, \(a_\alpha\to0\), \(H_\alpha\ge0\), and let \(f_\alpha\) be centered physical observable vectors. Set
\[
C_\alpha(t)=\langle f_\alpha,e^{-tH_\alpha}f_\alpha\rangle.
\]
Suppose \(C_\alpha(0)\to V>0\), \(C_\alpha(t)\to C(t)\) for every fixed \(t>0\), and \(C(t)\to V\) as \(t\downarrow0\). These are the minimal same-observable, nontrivial, time-continuous OS passage requirements. All \(C_\alpha\) are nonincreasing, by the positive spectral theorem.

**No-go proposition.** There is no regulator-independent \(q<1\) satisfying
\[
C_\alpha(2a_\alpha)\le q C_\alpha(0)
\]
for all sufficiently fine regulators.

**Proof.** For every fixed \(t>0\), eventually \(2a_\alpha<t\), hence
\[
C_\alpha(t)\le C_\alpha(2a_\alpha)\le q C_\alpha(0).
\]
Let \(\alpha\to\infty\) to obtain \(C(t)\le q V\). Then \(t\downarrow0\) gives \(V\le qV\), contradicting \(V>0\) and \(q<1\). QED.

This is **not** a counterexample to Yang--Mills. It rules out the **interpretation** of uniform original I7 as a contraction for the shrinking microscopic time \(2a_\alpha\) whenever the same observables have a nontrivial strongly continuous limit. Original16_FromI7.lean uses NonnegativeHeatCalculus at time \(2a\); the manuscript must establish whether this \(a\) is microscopic or a fixed physical-time parameter. If microscopic, the target must be repaired; never infer a cutoff-independent microscopic one-step deficit from a finite physical gap.

## 2. Exactly sufficient diagonal criterion at fixed physical time

Fix \(\tau>0\), independent of regulator. For each \(\alpha\), let \(H_\alpha\ge0\) on the nonvacuum physical Hilbert space \(\mathcal H_\alpha^\circ\) and \(T_{\alpha,\tau}=e^{-\tau H_\alpha}\). Assume \(0\le T_{\alpha,\tau}\le I\) and a dense centered Wilson-word family \(\{v_{\alpha,w}\}_{w\in W_\alpha}\).

Suppose a single \(m_*>0\), chosen before \(\alpha,w\), satisfies
\[
\forall\alpha,w\quad\exists C_{\alpha,w}<\infty:\qquad
0\le\langle v_{\alpha,w},T_{\alpha,\tau}^{n}v_{\alpha,w}\rangle
\le C_{\alpha,w}e^{-m_*\tau n},\quad\forall n\in\mathbb N.
\tag{D}
\]
There is NO uniformity requirement for the amplitudes \(C_{\alpha,w}\) in \(\alpha\), volume, support, word, or source coefficient.

**Diagonal spectral theorem.** (D) implies the full finite-complex-family I7 inequality, uniformly in every regulator:
\[
\langle F,(I-T_{\alpha,\tau})F\rangle
\ge(1-e^{-m_*\tau})\,\|F\|^2,
\qquad
F=\sum_{w\in S}c_wv_{\alpha,w}.
\tag{I7-phys}
\]

**Proof.** Write \(q=e^{-m_*\tau}\in(0,1)\). Let \(E_\alpha\) be the spectral resolution of \(T_{\alpha,\tau}\). For any \(\varepsilon>0\) with \(q+\varepsilon\le1\),
\[
(q+\varepsilon)^n\|E_\alpha([q+\varepsilon,1])v_{\alpha,w}\|^2
\le \langle v_{\alpha,w},T_{\alpha,\tau}^n v_{\alpha,w}\rangle
\le C_{\alpha,w}q^n.
\]
Divide by \((q+\varepsilon)^n\) and send \(n\to\infty\). The spectral projection annihilates every \(v_{\alpha,w}\); it annihilates their finite span and, by boundedness and density, all \(\mathcal H_\alpha^\circ\). Let \(\varepsilon\downarrow0\). Thus \(E_\alpha((q,1])=0\) and \(0\le T_{\alpha,\tau}\le qI\), which yields (I7-phys). QED.

**Research gain.** Do NOT begin with arbitrary mixed Wilson two-root covariance or all-family finite Gram estimates. Uniform long-time **diagonal** autocorrelation bounds for a dense family of individual centered Wilson words suffice. Positivity and spectral projection eliminate cross terms without an observable-uniform prefactor. A single plaquette is not dense, so a plaquette-only result still does not suffice. This is an abstract mathematical reduction, not a physical realization.

## 3. One exact remaining physical SU(2) input

The model-side RED target is now the following *single family* of inequalities in the true physical infinite-time Wilson/OS measure:
\[
\boxed{
\exists\,m_*>0\ \forall\,\alpha,w\
\exists\,C_{\alpha,w}<\infty\
\forall\,n\ge0:\quad
\big|\operatorname{Cov}_{\alpha}^{\rm Wilson}
 (W_w,\theta_{n\tau}W_w)\big|
\le C_{\alpha,w}e^{-m_*\tau n}.
}
\tag{YM-DIAG}
\]

The representation
\[
\operatorname{Cov}_{\alpha}^{\rm Wilson}
 (W_w,\theta_{n\tau}W_w)
 = \langle v_{\alpha,w},T_{\alpha,\tau}^n v_{\alpha,w}\rangle
\]
must be established for the same actual Wilson measure and same centered vectors, with finite periodic temporal wrap removed before \(n\to\infty\). The dense word family must include ALL gauge-invariant polynomial/cylinder vectors required by the physical OS Hilbert-space construction.

A candidate conditional rooted-polymer route has
\[
\mu=\kappa_*/(2(\chi+2)),\quad
a_\alpha L^{K(\alpha)}\le A,\quad
d_{\mathrm{root}}(w,n)\ge \tau n/A-b_{\alpha,w},
\]
and therefore the candidate rate
\[
m_*=\kappa_*/(2(\chi+2)A)>0.
\]
But the crucial hypotheses **are NOT known for the actual full physical SU(2) Wilson covariance**:
- common positive \(\kappa_*\), uniform smallness of complete infrared effective polymer activities (not merely old/new-R remainders), and uniform contact range;
- exact Wilson-source/connected-cluster dictionary including every effective infrared Gaussian/nonpolymer sector and source derivative, with any remaining error decaying in \(n\) at the same fixed positive rate;
- physical translation-to-root-distance geometry at arbitrarily large \(n\), with a time-independent amplitude, after removing temporal wrapping;
- real, nonnegative OS transfer moments, positive physical transfer at fixed \(\tau\), and density of the same Wilson-word family.

The public theorem Original24_BalabanTwoRootRealFullSeries proves a labeled two-root Mayer series for old/new-R activities **under** local-norm, geometry and graph inputs; it is not, by itself, an identity with the complete physical covariance. Original24_ConnectedRootDistance has an explicit distance estimate **under** its hPenroseDistance and hFP premises. Likewise, successful compilation of Original42_BookendCertificate retains I7 and the stated stage/model inputs as theorem arguments.

## 4. Lean / paper synchronization boundary

- No original theorem environment is promoted.
- No weakening, new axiom, sorry, admit, or claim of Clay solution.
- The prior conditional 39/39 acceptance ledger remains unchanged.
- A physical-clock version of Original16/Original42 would use \(t=\tau\) in NonnegativeHeatCalculus, rather than claiming \(\eta\) fixed for the shrinking \(2a_\alpha\) clock.
- Do not assert the diagonal spectral theorem is Lean-compiled until it has its own source and passing official-pin CI.
- No formal I7 proof or new CI is claimed by this note.
