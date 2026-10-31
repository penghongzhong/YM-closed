# Original 30: uniform bound for the source-derived joint distribution

Base remote commit: 980644ed0d6a472d5698272ed72b6674ec0d5c79.

The source-derived continuous joint distribution is now connected directly
to the previously certified actual Wilson all-volume estimate. For every
0<a<=1, arbitrary lattice size N, probability law mu and order r,

    ||T_(r,a,N)(F)|| <= 2 exp(24576 K) r! Q_(8r,8r)(F).

T is the actual coordinate-derivative reconstruction of the finite Wilson
exponential source, not a separately postulated moment family. Its exact
identification with the joint lattice expectation supplies integrability
and measurability, so no separate measurable-moment premise is needed.

K remains the explicit coefficient budget of each local Wilson polynomial.
The bound has no a or N on the right if the SAME K works for the regulator
family. The proof does not establish such a K for physically renormalized
coefficients; a^-d scaling and source mixing must be checked independently.
It also does not identify the physical RG polymer chart or construct a
continuum common-filter limit. This weighted bound has spatial weight 8r;
it is not the fixed-q interface OS_E0prime.

Lean 4.35.0-rc3 / Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.
Audit: tools/verify_original30_source_uniform.py; full types, actual source
and joint-distribution definitions, standard axiom audit, kernel replay,
and dependency source hashes in verification/original30-source-uniform-20261031.

Original 30 remains OPEN; original conditional ledger remains 37/39.
Original 24 remains open; I7 remains an explicit unproved premise.
