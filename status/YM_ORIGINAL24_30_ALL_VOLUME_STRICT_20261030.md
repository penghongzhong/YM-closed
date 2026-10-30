# YM-closed / Original24 and Original30 — 2026-10-30 strict status

## Unchanged original-environment count
**37/39 = 94.87%**, historical official-pin conditional original environments.
Only original manuscript environments **24 and 30** remain unverified.

The 37 include published-external-implication interfaces and source-
hypothesis-assisted conditional theorems: they are not 37 unconditional
physical SU(2) Yang–Mills theorems. **I7 remains an explicit, unproved
mathematical input**. No `sorry`, `admit` or custom axiom has been
introduced by this continuation.

Lean: `leanprover/lean4:v4.35.0-rc3`.
Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
Public branch: `ym-original24-link-wilson-20261030`.

## New verifications — genuine sitewise SU2 link variables
- [Actions #40990364337](https://github.com/penghongzhong/YM-closed/actions/runs/40990364337)
  SUCCESS. `YMOriginal/Original24_ActualLatticeLinks.lean`
  proves gauge-covariant actual ordered link holonomies; all interior
  site gauge factors cancel. Closed-loop roots and arbitrary finite
  Wilson word polynomials are invariant under independent
  gauge transformations at every vertex. No common-basepoint gauge
  surrogate is needed.
- Only standard Lean axioms printed.

## New verified raw Wilson source / continuum-volume estimates
- [Actions #40991353443](https://github.com/penghongzhong/YM-closed/actions/runs/40991353443)
  SUCCESS. Actual joint `4r` Schwartz test at each configuration,
  finite `6 N^4` plaquettes, physical `a^(4r)` quadrature and explicit
  actual SU2 finite-word polynomial coefficients; independent of UV
  spacing for a bounded physical `R`.
- [Actions #40991585141](https://github.com/penghongzhong/YM-closed/actions/runs/40991585141)
  SUCCESS. Construct the genuine continuous joint `4r` Schwartz
  source linear maps and deduce fixed-box E0prime growth; no assumed
  source analyticity.
- [Actions #40991862980](https://github.com/penghongzhong/YM-closed/actions/runs/40991862980)
  SUCCESS. Genuine probability-space expectation of joint Wilson
  moments, with exact bare finite-box bound and measurability as the
  only probability-theoretic input.
- [Actions #40992865321](https://github.com/penghongzhong/YM-closed/actions/runs/40992865321)
  SUCCESS. Exact FOUR-dimensional lattice inverse-square spatial
  cubature `sum_{orientation=1..6, n in [0,N)^4}
  prod_i a/(1+a*n_i)^2 <= 96`, uniform in `0<a<=1`,
  `N`, and the physical size `N*a`.
- [Actions #40995044143](https://github.com/penghongzhong/YM-closed/actions/runs/40995044143)
  SUCCESS. Actual physical Euclidean site geometry gives
  `prod_i (1+a*n_i)^2 <= 128 (1+||a*n||^8)`.
  Thus for genuine SU2 finite Wilson-word polynomials `O_p(U)`
  with uniform BARE template budget `K`,
  `||sum_p a^4 f(a*n(p)) O_p(U)|| <=
      12288*K*(p_(0,0)(f)+p_(8,0)(f))`.
  No N or `a` or physical box radius appears in the constant.
- [Actions #40995492521](https://github.com/penghongzhong/YM-closed/actions/runs/40995492521)
  SUCCESS. Two new strictly audited all-r mixed-bare-source theorems:
  `actual_bare_wilson_all_order_uniform` and
  `actual_bare_wilson_probability_all_order`.
  For each r and Schwartz tests f_1,...,f_r, the same correlated
  SU2 link configuration U and any genuine probability measure
  satisfying observable measurability,
  `|E prod_j Phi_a(f_j)| <=
       (12288*K)^r * prod_j (p_(0,0)(f_j)+p_(8,0)(f_j))`.
  No independence or Gaussianity of the Wilson link measure assumed.
- The successful actions' `#print axioms` output lists only
  `[propext, Classical.choice, Quot.sound]`.

## Exact remaining Original24 and Original30 barriers

**Original24**: The strict finite SU2 external-word source and B10
fifth-order Taylor/placement chain are certified, including sitewise
gauge invariance. The actual physical old/new-R histories still must
be identified with the exact U1/CMP119/CMP122 local activity,
correct history/root-distance norms and projection/jet classes at
fixed D, and original `C-LOCAL-POLY-LFD=CLOSED` declaration. The
required analytic inputs cannot be passed as a reformulated instance
of the desired conclusion.

**Original30**: Current new moment and spatial estimates are for
**bare bounded Wilson-word observables weighted by a^4** and a
positive-quadrant site representation. These data are not yet the
physical renormalized D=4 source with canonical a^(-d), source/jet
counterterms and all RG weak-stop source chart; the uniform **bare
coefficient budget K does not imply a renormalized coefficient
budget**. The same-net continuum source normalization, full joint
Schwartz OS E0prime test extension and nontriviality/mass-gap
conclusion remain unproved. Bounded cutoff moments alone do not
establish their nonzero physical continuum limit.

In particular, a bound on pure tests
`prod_j p_8(f_j)` does not by itself automatically produce an
unchanged `4r` joint Schwartz bound with a fixed weight index
for every r; the required projective tensor/Schwartz topology
control must be checked explicitly.

## Next shortest dependency nodes
1. Match actual `a^{-d}` source and fixed-D filtered jets to the
   verified bounded Wilson-word data at every weak RG step, proving
   the needed cancellation/renormalized source estimates.
2. Reuse actual old/new-R U1/U2 rooted-model data in Original24
   using the SAME native root distance and B10 local projector,
   not a surrogate `hB10`.
3. Establish Original30 full all-order JOINT
   Schwartz/test projective bound on the renormalized source, and
   same-net continuum moment convergence.
4. Only after Original24/30 are genuinely closed, return to
   proving I7 and auditing every remaining conditional model input.

Do not promote the original-environment count above **37/39**
on the strength of the new supporting certificates alone.
