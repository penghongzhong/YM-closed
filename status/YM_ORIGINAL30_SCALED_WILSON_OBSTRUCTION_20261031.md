# Original 30: obstruction to a bare pointwise UV bound

In `YMOriginal/Original30_ScaledWilsonObstruction.lean`, the element `-I`
is constructed inside the actual `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
The existing `wilsonRoot` satisfies `wilsonRoot (-I) = 4`. Consequently,
for the scalar example `a⁻⁴ wilsonRoot(U)`, there is no constant K
uniform over every `0 < a ≤ 1` and every U in SU(2). The quantified
statement is `no_uniform_scaled_root_bound`.

This is a narrow counterexample to using the bare uniform pointwise bound
for this naively scaled root. It does not rule out a bound for a correctly
renormalized source, a subtracted observable, a measure-averaged estimate,
or an estimate using cancellations. It does not prove a statement about
any specific manuscript composite observable without the source dictionary.
Original 30 remains open; no original environment is promoted.

The actual model source/RG matrix, its O(g_j^4) residual, the activity
budget, the all-order joint Schwartz norm and same-net continuum identity
remain to be established. I7 remains an explicit unproved hypothesis.

## Local verification

The source was compiled with `lean -DwarningAsError=true` and replayed by
`leanchecker -v`; both exited 0. A separate audit imports the produced
olean and prints the complete elaborated declaration types and transitive
axioms. The two declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorryAx`. Logs and audit source are in
`verification/original30-scaled-wilson-obstruction-20261031/`.
Toolchain: Lean 4.35.0-rc3, Mathlib
`516d31250e96c4e8e76888c3d8e2e43a9642b9ee` (tracked tree clean).
Source SHA256:
`8228d6e55ee309258aede86138e6b0c4328ff00bb6e88c1051fb36721c707722`.
