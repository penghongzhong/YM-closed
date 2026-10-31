# One verified log-source-to-full-moment theorem

The new theorem is
`YMUIC.Original30.polymer_source_normalized_moments`, in
`YMOriginal/Original30_PolymerSourceMoments.lean`.

For a finite polymer set Gamma, suppose each complex activity is analytic on
the source ball of radius rho > 0 and bounded there by a weight. Assume the
sum of these weights is at most A >= 0. The theorem constructs

    H(J) = sum_{i in Gamma} activity_i(J)
    Z(J) = exp(H(J) - H(0))

and proves analyticity of Z, Z(0) = 1, and, for every natural r including zero,

    ||D^r Z(0)[h_1,...,h_r]||
      <= e * r! * (e * (1 + 2*A) / rho)^r * product_j ||h_j||.

The derivative is the actual iterated Frechet derivative of the constructed
normalized generating function. No full-moment estimate, cumulant estimate,
moment/derivative dictionary, or analytic bound on Z is an input.

The proof uses the Schwarz lemma to control H(J)-H(0), restricts to the source
radius rho/(1+2*A), bounds Z there by e, and applies the existing verified
Banach-space Cauchy estimate. Dependence on A is polynomial of degree r.
This avoids a support-dependent exponential prefactor when A grows with the
support. It does not itself construct a global joint Schwartz extension.

## Executed validation

- Lean 4.35.0-rc3.
- Mathlib commit 516d31250e96c4e8e76888c3d8e2e43a9642b9ee; tracked tree clean.
- Targeted Lake compilation with warnings treated as errors: passed.
- Full, untruncated elaborated type and axiom audit: passed.
- Independent `leanchecker -v` kernel replay: passed.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, new axioms, `unsafe`, or `partial` in the project
  source dependency closure of this theorem.

Reproduction command with the pinned Lean on PATH:

    python3 tools/verify_original30_polymer_source_moments.py

Machine-readable results, full type, compressed audit output, kernel replay,
and source hashes are in
`verification/original30-polymer-source-moments-20261031/`.

## Scope and ledger

This passes one new analytic theorem, not an additional complete manuscript
environment. The original conditional ledger remains **37/39**. Original 24
and Original 30 remain open; I7 remains an explicit unproved hypothesis.

Still required for Original 30: identify these source activities and their
derivatives with the actual renormalized Yang--Mills generating function,
prove the required regulator-uniform input estimates, obtain the full joint
Schwartz extension with the correct OS norm, and pass along the same
continuum net. No bare Wilson estimate discharges these requirements.

The earlier bare joint estimate at commit
862c350b697f13657acf73066f50223aa869c8d8 largely duplicates results already
present on `ym-original30-joint-all-volume-20261030` (head
38594f72db2f92b2fb624b4d0edbe73c90346749). That estimate is not counted again.
The present theorem addresses a different step: analytic polymer log sources
to normalized full moments. No manuscript or private archive is published.
