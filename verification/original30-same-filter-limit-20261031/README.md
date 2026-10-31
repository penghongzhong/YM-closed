# Same-filter joint limit: audit

Target `YMUIC.Original30.joint_same_filter_limit`, source SHA-256
`533241223eab7a274b521b76df052a641fbdbd7c35d178077a447e277bd2ea83`.
Lean 4.35.0-rc3; Mathlib `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.

Compilation with `lean -DwarningAsError=true -o ...` exit 0, untruncated
`#check` and `#print axioms` using `pp.maxSteps 10000000` exit 0,
and `leanchecker -v YMOriginal.Original30_SameFilterLimit` exit 0. Axioms
are `propext`, `Classical.choice`, `Quot.sound`; no sorryAx.
The build used the existing original worktree `.lake/build` import objects
and the fixed Mathlib checkout; only this new olean was added there.

The theorem assumes all orders converge pointwise on the same nontrivial
filter and have the indicated uniform joint Schwartz seminorm bounds. It
constructs continuous linear limits, proving linearity and continuity, and
preserves the bounds. It does not construct the physical renormalized net,
prove its convergence, or identify its limit with Yang--Mills Schwinger
functions. Original 30 therefore remains open.
