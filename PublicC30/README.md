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
smooth-series theorem. These claims remain pending until the dedicated
public Lean CI returns success and the axioms are audited.
