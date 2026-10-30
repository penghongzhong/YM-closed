# YM-closed — Original30 joint all-volume OS-growth bridge (2026-10-30)

## Audited source, strict pin, evidence

Public isolated branch: ym-original30-joint-all-volume-20261030
Base: ym-original24-link-wilson-20261030, commit a8deb90ecc310032fb2c517ecde4e7a31d4528d8.
Pin: Lean 4.35.0-rc3 / Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

Successful STRICT GitHub Lean runs:
- #41015798641: entire joint 4r-dimensional Schwartz bound for genuine bare
  SU2 Wilson word sources, uniform in all UV cutoffs and physical volumes;
  uses explicit point geometry premise.
- #41016255617: canonical physical 4r joint coordinates constructed and
  proved to dominate each true lattice 4D site. No geometric premise remains.
- #41016741714: actual continuous SchwingerHierarchy all orders assembled
  from same actual bare SU2 lattice configuration, with linear-in-order
  spatial-weight single factorial bound.
- #41017777483: independently type-checked and kernel-compiled
  OS II 1975 linear-order Schwartz growth certificate; full statement
  and axiom print passed (only propext, Classical.choice, Quot.sound).
Actions: https://github.com/penghongzhong/YM-closed/actions/runs/41017777483

Sources:
1. YMOriginal/Original30_JointProductSchwartzDecay.lean
2. YMOriginal/Original30_AllVolumeJointWilson.lean
3. YMOriginal/Original30_CanonicalJointLocations.lean
4. YMOriginal/Original30_AllVolumeBareHierarchy.lean
5. YMOriginal/Original30_OS1975LinearOrder.lean
Workflow: .github/workflows/ym-original30-joint-volume.yml

## Exact proven theorem

Let W = SU(2), 0<a<=1, N in Nat, r in Nat, and F in Schwartz(R^(4r)).
Use the SAME actual SU2 configuration in every insertion, arbitrary
fixed finite polynomial templates of ordered Wilson-word holonomies,
a^4 source quadrature, and a uniform bare coefficient budget K >= 0.
Define S^(bare)_(r,a,N)(F) by the literal 4r joint lattice cutoff sum,
with canonical concatenated spatial coordinates. Then the Lean checker
proves simultaneously:

  ||S^(bare)_(r,a,N)(F)||
     <= (24576 K)^r ( p_(0,0)(F) + p_(8r,0)(F) ),

and a continuous full-joint SchwingerHierarchy with the uniform
linear-order Schwartz E0'-shaped growth

  ||S^(bare)_(r,a,N)(F)||
     <= 2 (1+24576K)^r r! P_(8r,8r)(F).

The norm constants have NO UV/physical-volume factor.
The canonical coordinate norm inequality is proved by an actual
Fin(4) -> Fin(4*r) injective map and Euclidean squared-norm sums;
not an abstract geometry hypothesis. The r! upper bound is a
controlled surplus to the directly proved exponential bound.

## Original OS II source verification

Osterwalder--Schrader (1975), CMP 42, p.287, Sec. IV.1, Eq. (4.1),
uses a distribution Schwartz test norm with order s*n (both spatial
weight and differentiation), together with factorial-growth constants.
URL: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II-with-an-Appendix-by/cmp/1103899050.pdf

The repository's historical conditional Original34 interface,
YMOriginal/Original34_OSII_ExternalInterface.lean, instead defined
jointSchwartzControl r q (k*r) with FIXED spatial weight q.
That premise is STRICTER than this bare all-volume certificate.
Consequently the 2026-10-30 new module defines an independent
jointOS1975LinearOrderGrowth with jointSchwartzControl r (s*r) (s*r).
It does not replace, weaken or claim to satisfy the old stronger
OS_E0prime interface. The published OS-II application should
eventually use the exact verified 1975 linear-order format.
The previous conditional Original34 theorem remains logically
valid under its stronger assumptions, but physical applicability
still depends on correct model/test-space input.

## Precise remaining physical original30 obligations

1. The actual canonically normalized curvature/Wilson local composite
   source of the C29 manuscript has a^-d and counterterm/RG mixing,
   unlike the BARE a^4-weighted bounded Wilson word. Prove true
   regulator-uniform source coefficients and radius after correcting
   engineering dimensions, rather than assuming a uniform K for the
   renormalized source.
2. Derive actual polymer source chart analyticity and RG weak-stop
   all-r cumulants with uniform radius and rooted counting for the
   same physical source; generic bare Wilson bounds are insufficient.
3. Show same-net UV/volume continuum Schwinger limits and exact joint
   test compatibility. Current finite-regulator distributions need
   not have a nonzero unique physical limit.
4. Match the exact published OS II E0' domain and norms (including
   Schwartz functions away from diagonals and factorial coefficient
   growth), and preserve E1--E4 and S0 normalization.
5. Original24 requires full physical connected polymer Ursell/FP
   identification, correct U1/R histories, source jet and B10
   renormalized localization; unrelated to proof of this bare
   Original30 theorem.

## Unchanged original-environment accounting

Historical official-pin CONDITIONAL per-original-environment union
37/39 = 94.87%. Only original IDs 24 and 30 remain unverified.
Original1/34 are published external-interface conditional statements,
Original42 is conditional on unproved I7 and other stated physical
model/continuum input. The new auxiliary declarations herein do NOT
promote the manuscript count to 38/39. No unconditional 4D SU2 mass
gap or full continuum UIC proof is claimed. I7 remains open.
