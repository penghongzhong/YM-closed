# Original 30: same-filter extension from generating test atoms

Base remote commit: 9f0e28d77bb42aec454f0801e3e147c9ebec31c5.
Lean 4.35.0-rc3 and Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

The previous `joint_same_filter_limit` assumed convergence on every joint
Schwartz test. The new terminal theorem
`YMUIC.Original30.joint_atom_same_filter_limit` only assumes convergence on
an atom set A_r whose complex linear span is dense in the joint Schwartz
topology. It proves convergence on finite linear combinations, then on all
joint tests, constructs continuous linear limits, and proves uniqueness of
the entire hierarchy. All orders use the same original nontrivial filter;
no subsequence or order-dependent subnet is chosen.

For arbitrary functions q(r), m(r) and C(r), an input bound

    ||T_(r,i)(f)|| <= C(r) Q_(q(r),m(r))(f)

is retained exactly in the limit. There is no added factorial or spatial
weight loss. The proof restricts to the dense subspace, constructs its limit
linear map, proves continuity from the given seminorm bound, extends this
map by completeness of C, and uses equicontinuity to obtain convergence on
the closure. The only project helper on its proof chain is
`dense_test_same_filter_limit`, in its own Lean file. The older common-filter
lemma is not imported into this new proof chain.

Actual atom-span density, the joint regulated uniform bound, and convergence
on the actual atoms remain explicit model/test-dictionary obligations. In
particular, the existing torus C2 coordinate reconstruction alone has not
been identified with a dense subset in the full joint Schwartz topology.
The uniform physical source analytic radius and renormalized-source
identification are also not proved here. This is a conditional extension
theorem, not an acceptance of the physical original environment.

Run `python3 tools/verify_original30_atom_limit.py` with the pinned Lean on
PATH. The local runtime used LD_PRELOAD=/tmp/ym-lean/proc-self.so only for
process-executable path lookup. Targeted warnings-as-errors builds, complete
untruncated types, standard-foundation-only axiom checks, both leanchecker
replays, and project dependency source hashes are recorded in
`verification/original30-atom-limit-20261031/summary.json`.

The conditional original ledger remains 37/39. Original 24 and 30 remain
open; I7 is still an explicit unproved premise.
