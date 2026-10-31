# Original 30: source-support shell count to full moments

Lean 4.35.0-rc3; Mathlib `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
The theorem `local_source_moments_from_shell_count` combines local-source
cancellation with an explicit finite-shell geometric summation. Given
`σ<κ`, nonnegative `ε,C`, the stated local analyticity and source locality,
and for every length `m` and active polymer `X` the bounds

    |E_J(X)| ≤ ε exp(-κ length(X)),
    #{active X : length(X)=m} ≤ C exp(σ m),

it proves the normalized full-source all-order derivative bound with

    A = ε C / (1 - exp(-(κ-σ))).

`A` is derived by grouping the finite active set into exact length fibers
and summing the geometric majorant. The original activity and count bounds
are explicit theorem premises; this does not establish they hold for the
physical Yang--Mills RG polymers. Physical source locality, normalization,
uniformity and the common continuum limit remain to be proved. No original
environment is newly accepted.

Checks:

- `lake build YMOriginal.Original30_LocalSourceShellBudget`: exit 0, Lake
  used `-DwarningAsError=true`.
- `lake env lean -DwarningAsError=true verification/original30-local-polymer-shell-20261031/ExactTypes.lean`:
  exit 0; full types and axiom output are in `exact-types-axioms.log`.
- `lake env leanchecker -v YMOriginal.Original30_LocalSourceShellBudget`:
  exit 0; evidence is in `kernel-replay.log`.
- Both declared theorems depend only on `propext`, `Classical.choice` and
  `Quot.sound`; no `sorryAx` or new axioms. Source SHA-256:
  `3e910781c973b38a9c3fc0e89ac7049318b76207c448e7e4a14db7af6919929b`.
