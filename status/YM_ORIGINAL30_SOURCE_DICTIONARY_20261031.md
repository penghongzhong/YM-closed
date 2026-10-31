# Original 30: exact finite Wilson source / joint-test dictionary

Base remote commit: a38a9a6e70ed1bb5c865d0bb3d36ab66d7abc748.
Lean 4.35.0-rc3 and Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

For the SAME arbitrary probability law on SU(2) link configurations, use
actual ordered Wilson-word polynomials O_p and the actual generating map

    Z(J) = integral exp(sum_p w_p J_p O_p(U)) dmu(U).

The finite label set, weights, word templates and complex coefficients are
explicit. They may depend on the regulator. No uniform coefficient budget
is imposed in this exact identity theorem.

The proof constructs each O_p as a bounded continuous observable. Its bound
is derived from the existing SU(2) word-polynomial bound, and its continuity
is proved from continuous link coordinates by induction on actual ordered
words and monomials. The finite source is then a continuous linear map into
the commutative Banach algebra of bounded continuous complex observables.
Expectation is a continuous complex linear map of norm at most one.

The Banach-algebra exponential series and its symmetrized coefficient
formula give every derivative at zero; the permutation factorial cancels
the Taylor coefficient factorial exactly. Continuous linear composition
with expectation proves

    D^r Z(0)[h_1,...,h_r]
      = integral product_j (sum_p w_p h_j(p) O_p(U)) dmu(U).

This is proved for arbitrary r, including r=0. It establishes analyticity
on the entire finite source space and Z(0)=1. No interchange of derivative
and integral, analytic-source certificate, or moment dictionary is assumed.
The same configuration U occurs in every factor, so correlations are kept;
there is no independence or Gaussianity assumption.

Let e_p denote the actual coordinate basis of the finite source space. For
an arbitrary general joint Schwartz test F, define the continuous linear
functional

    T_r(F) = sum_(p_1,...,p_r) D^r Z(0)[e_(p_1),...,e_(p_r)]
                                   F(x_(p_1,...,p_r)).

The terminal theorem proves integrability and the exact equality

    T_r(F) = integral actualWordJointCutoff(r,w,U,words,coeff,locations,F) dmu(U).

Thus the constructed distribution acts on all joint tests, not only
factorized tests, and is identified with the already-existing actual
finite lattice moment. The general joint reconstruction here is a finite
coordinate sum, not an assumed infinite Fourier/tensor representation.

Scope boundary: entire analyticity at each finite regulator does NOT give
a regulator-uniform bound on a fixed source ball. These theorems neither
identify this source with the physical renormalized RG polymer source nor
handle additional nonlinear source counterterms. They do not prove a
regulator-uniform renormalized joint seminorm estimate or the actual
continuum/infinite-volume common-filter limit. Although weights and
coefficients may be cutoff dependent, their physical normalization and
uniform budgets remain to be proved.

Run `python3 tools/verify_original30_source_dictionary.py` with the pinned
Lean on PATH. The audit records strict builds, complete theorem types,
axiom checks, five kernel replays, and recursive project source hashes in
`verification/original30-source-dictionary-20261031/summary.json`.

Original 30 remains OPEN. Original-environment conditional ledger: 37/39,
unchanged. Original 24 is also open; I7 remains an explicit unproved premise.
