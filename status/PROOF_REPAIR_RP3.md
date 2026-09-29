# RP3: original Wilson score cost and physical Gram optimization

Date: 2026-09-29. Research parent: RP2; initial repository head 9152bf8f21d008e8edacbaf1ec17f6d35058b3df.

## Status boundary

I7-GLOBAL-ROOT-FRAME remains OPEN. This is a status-only commit. No Lean source, toolchain, dependency pin, workflow, repository visibility, or existing certification is changed. New Lean PASS count: 0. The continuous-measure statements below have not been verified end to end in Lean.

## New private proof work

The private CURRENT adds nine formal nodes in Section 24:

- lem:RP3-Lie-contractions: exact right-invariant SU(2) differential commutator, contractions, and weighted adjoint identities.
- thm:RP3-exact-cost: the original initial-slice raw-score Gram equals the symmetrized second-derivative Gram plus the Lie-curvature term and the full original action-Hessian contraction. All cross terms are retained.
- lem:RP3-Fisher-cancellation: the Hessian of the negative log slice marginal plus the conditional score covariance equals the conditional expectation of the raw action Hessian. Distant cross-covariances are not individually discarded or assumed zero.
- prop:RP3-shared-Wilson: an exact shared-hidden-link Wilson model exhibits nonzero off-diagonal conditional covariance and its cancellation. This model is not substituted for the full four-dimensional measure.
- lem:RP3-plaquette-Hessian: original oriented plaquette word differentiation gives a local incidence bound for the action Hessian. Four spatial and two temporal plaquettes give c_star <= 9 beta / 2 for one varied spatial slice.
- thm:RP3-volume-free-cost: the raw-score squared norm is bounded by the symmetrized Hessian norm plus (1+9 beta)/2 times the gradient norm, in the original interacting marginal. There is no additional volume, link-count, test-family-size, or time-window-length prefactor. Beta-dependence and both derivative norms remain.
- cor:RP3-physical-matrix and cor:RP3-compressed-optimum: finite physical Gram bounds retain the action matrix and the favorable conditional-projection residual. Explicit Moore-Penrose inverses act only on displayed finite source-cost matrices; range conditions and singular cases are proved rather than assumed.
- prop:RP3-background-spectra: exact identity and central pi-flux configurations of an original finite four-dimensional slab give opposite action-Hessian spectra. This excludes an unconditional pointwise-positive-curvature shortcut, not the Yang--Mills mass-gap claim.

## What is still missing

The derivative-cost upper bound is NOT a norm coercivity estimate or an I7 certificate. The exact action contribution and residual must still produce a regulator-, volume-, UV-cutoff-, and finite-family-independent positive physical Gram lower bound at the same physical time window. The auxiliary marginal generator is not identified with the physical Hamiltonian. No static/global Poincare replacement, heat-kernel-action substitution, frozen-occurrence enlargement, or disposal of peak/outward/off-cycle mass is used.

## Computation and document evidence

- RP3 exact SymPy algebra checks: 64/64 PASS.
- Re-executed RP2 exact algebra regression: 36/36 PASS.
- Numerical diagnostics: original 72-by-72 slab Hessians at identity, central pi-flux, and eight deterministic random configurations; additional finite-volume Fourier diagnostics. Random configurations are not Gibbs samples. Floating-point computations are not interval certificates or proof inputs.
- New private PDF: 85 pages. Nine new theorem/lemma/proposition/corollary environments. Final LaTeX build has no warnings, overfull boxes, or underfull boxes; new pages have been rendered and inspected.
- Static references: 811 unique labels, zero duplicate/missing/explicit forward references. These are static metrics, not whole-manuscript semantic certification.

Private CURRENT TeX SHA256: 78d01d217452997cf9a8d4f95b6ea8620cb24cf3cc0d124633b9c2614aa9af43.
Private CURRENT PDF SHA256: 70c04503b5a0d5abc0531c1187db378de956974eda7637a4a84094eccd8f89c2.

TeX/PDF, proof details, computation scripts, and the private audit bundle remain in ChatGPT /YM; no manuscript files or PDF artifacts are added to this public repository. Frozen v128 is unchanged.
