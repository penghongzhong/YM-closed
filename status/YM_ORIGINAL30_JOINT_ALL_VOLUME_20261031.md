# Original30: actual joint bare Wilson moments, all volumes

The original conditional ledger remains **37/39**. Original24 and Original30
are open; I7 remains an explicit unproved global hypothesis. The result below
is not an acceptance of either original environment.

## Exact statement

For each r and N, 0<a<=1, and the actual concatenated 4r-dimensional positions
of r plaquettes in the existing nonnegative a*Fin(N)^4 lattice chart,

    | E_mu[ S_bare_(r,a,N)(F) ] |
      <= (24576 K)^r [p_(0,0)(F) + p_(8r,0)(F)].

Here F is one arbitrary Schwartz function on R^(4r), not a pure tensor.
Every plaquette insertion is the existing ordered SU(2) Wilson polynomial,
with its explicit template budget at most K. The same lattice configuration
occurs in all slots. The law mu may be any probability measure; only
measurability of the actual observable is required. Its integrability is
proved. The right-hand side contains neither N, a, nor a physical box radius.
The theorem also covers r=0 and the empty-volume cases by the existing finite
sum conventions.

## Proof chain

1. Each actual lattice coordinate is bounded by the norm of its concatenated
   joint position.
2. The full cubature denominator is bounded by
   256^r (1 + |x|^(8r)).
3. The genuine 4r-dimensional Schwartz weighted evaluation estimate pays for
   that denominator. No four-dimensional-only lemma is reused at a different
   dimension.
4. The existing true four-dimensional plaquette cubature is at most 96.
   The exact finite product/sum identity gives 96^r for r slots.
5. The actual Wilson polynomial norm and probability integration give the
   displayed estimate, with 256*96=24576.

## Verification

Run `python3 tools/verify_original30_all_volume_joint.py` using the fixed
Lean 4.35.0-rc3 toolchain and Mathlib
516d31250e96c4e8e76888c3d8e2e43a9642b9ee. The script builds with warnings as
errors, prints every new complete declaration type and its transitive axioms,
checks for output truncation and forbidden axioms, replays the module with
leanchecker, and records source hashes. The final receipt is
`verification/original30-all-volume-joint-20261031/summary.json`.

## Exact remaining original-environment obligations

This is a **bare** Wilson moment theorem. It does not establish the canonical
a^(-d) source normalization, actual source counterterm/jet matching, or a
same-net continuum Schwinger hierarchy. Those cannot be replaced by the
bare coefficient budget K.

There is also an explicit type mismatch in the current route to the existing
`OS_E0prime` interface: that definition fixes the spatial weight q independently
of r and uses derivative orders through k*r. This proof needs spatial weight
8*r. No uniform-in-r conversion is claimed. The interface and its manuscript /
published norm dictionary must be checked before using this result in
Original30 or Original34. The old definition and old acceptance ledger have
not been changed here.

The relevant original reference is Osterwalder--Schrader,
Commun. Math. Phys. 42 (1975), 281--305, norm (2.1) and growth conditions
(4.1)--(4.2). An explicit norm-equivalence proof is still required; a name
match with that theorem is insufficient.

Next work should inspect the actual renormalized source formula and the
published/manuscript Schwartz norm dictionary directly. Further bare moment
helpers cannot by themselves increase the original-environment numerator.
