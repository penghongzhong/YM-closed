# Public Yang–Mills U–I–C verification workstream: Original 30

This **public branch** contains a small, independent Lean 4.35.0-rc3 proof
of the maximum-shell **arithmetic** estimate used in the attempt to prove
joint Schwartz/Fourier growth. It is not a proof of the Yang–Mills mass gap.

Exactly two theorem environments are targeted:
- `scaled_shell_exponent_budget`: exponent bookkeeping for 4r-coordinate source localization;
- `scaled_shell_power_budget`: its positive-real power inequality.

The separate model obligations remain open: Schwartz-to-torus
periodization and its derivative chain; uniform Wilson local `C²` source norm;
actual polymer/Schwinger test-function correspondence; OS reconstruction;
the I7 global-frame inequality and full dependency closure.

**Do not count either theorem as completion of manuscript Original 30.**
The inherited, standard-input-assisted 34/39 ledger is not a certificate of
unconditional YM U–I–C. No paper/TeX/private verification logs are copied here.

## 2026-10-29: public six-module Schwartz dependency closure

The unchanged Lean sources in `YM/OSTensor/` establish directional,
iterated and mixed fourth-order Schwartz seminorm estimates, concluding in
`schwartz_mixed_joint_control`. Every imported `YM.*` module required
by this particular theorem is included; the source blobs match the
already-existing project code. The official-pin public CI builds the import
closure and audits the exact terminal theorem's axioms. It **does not** assert
that Wilson source periodization, the coefficient budget or manuscript
Original 30 has been completed.

## 2026-10-29: ten-module multidimensional Fourier dependency closure

The unchanged `YM/OSTensor/Fourier*.lean` and `ProductSeries.lean`
modules prove periodic coordinate derivatives, the multivariate fourth-order
frequency decay, and absolute weighted second-order Fourier summability.
All ten transitive `YM.*` imports for the terminal Fourier theorem are
included. This is an analytical bridge, **not** the actual periodization
of Wilson-Schwartz sources and not proof of manuscript Original 30.

## Actual Fourier atoms: real coordinate derivatives

The public proof now targets a new exact, arbitrary-dimensional theorem computing
real-coordinate derivatives of the **actual** torus Fourier modes. It also
constructs every iterated derivative-chain element and the pointwise unit norm.
The goal is the local `C²` source atom estimate, not yet the Wilson dictionary.

## 2026-10-29 additional C² formalization targets (pending CI)

The next source batch proves actual Fourier-coordinate derivative growth up to
order 2, a full mixed frequency product budget, Banach-valued Fourier jet
summability and termwise differentiation of the series by the standard
smooth-series theorem. These proofs passed official-pin CI #40851315206 with standard axioms only.

## Actual periodic C² reconstruction, verified #40852461789

The next file derives ordinary coefficient summability from the joint
fourth-order bound, identifies the zero-order Fourier series with the actual
periodic input using Mathlib Fourier uniqueness, and reconstructs its first
and second real-coordinate derivatives by summing differentiated modes.
The outstanding model-specific periodization and Wilson C² maps are not
proved by this result.

## Next verification target: actual smooth dyadic shell and annular margins

Sources `YM/OSGrowth/Cauchy.lean`, `DyadicCutoff.lean`, `DyadicShellAnnulus.lean`,
`DyadicCutoffDerivativeBound.lean`, `DyadicShellRegularity.lean` are unchanged
Git blobs from the inherited research proof tree. The new terminal
`ScaledDyadicShellMargin.lean` proves exact uniform inner and outer radial
margins after scale `2^(n+4)`: the shell vanishes if `‖y‖≤1/16` or
`‖y‖≥1/4`. This is an analysis prerequisite to periodicization;
it is **not** a constructed periodic map or actual Wilson source dictionary.
This next batch is pending official pinned CI.

## 2026-10-29: direct one-coordinate dyadic shell periodization

`ScaledDyadicShellCircle.lean` constructs a genuine continuous unit-circle
function from the existing rescaled dyadic shell by matching the endpoints of
`[-1/2,1/2]`. It proves exact equality on the fundamental interval and
uses the already-established strict annular support margins. This is one
real coordinate only; the multivariate smooth periodization and actual Wilson
source dictionary remain open until separately constructed and audited.
