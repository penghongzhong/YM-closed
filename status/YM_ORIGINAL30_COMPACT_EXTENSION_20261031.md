# Original 30: concrete compact-test density and Schwartz extension

Base remote commit: a0924312d0d99fff3d298162fd9204f1f81d1473.
Lean 4.35.0-rc3 and Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

This change proves a concrete density input which the preceding atom-limit
bridge assumed. It uses the project's actual dyadic smooth cutoffs chi_n,
equal to one on the ball of radius 2^n and supported in the ball of radius
2^(n+1). For every complex Schwartz test f, spatial weight k and derivative
order m, it proves

    p_(k,m)(chi_n f - f)
      <= 2^(-n) sum_(i=0)^m binom(m,i)
           [p_(0,i)(chi_0) + 1] p_(k+1,m-i)(f).

The coefficient is independent of n. The proof uses the existing exact
rescaling bound for all derivatives of chi_n, the iterated Frechet Leibniz
estimate, and one additional spatial weight outside the inner ball. In the
inner ball, the error and all its derivatives vanish locally. This yields
convergence in EVERY Schwartz seminorm, not merely C2 or pointwise
convergence. Each approximant has actual compact support. Consequently,
actual smooth compactly supported tests are dense in the full Schwartz
topology, including the joint space in 4r dimensions.

`compact_schwartz_extension` starts with a complex linear functional L on
the concrete submodule of compactly supported Schwartz tests. Given one
continuous seminorm P and the bound ||L f|| <= C P(f), it derives continuity
and a unique continuous extension to all Schwartz tests. The extension
preserves the SAME bound. Neither density nor continuity of L is assumed.

`joint_compact_same_filter_limit` applies this construction at every order
and regulator. Its inputs are linear functionals defined ONLY on compact
joint tests, a bound C(r) Q_(q(r),m(r)) uniform in regulator AND support, and
convergence on these compact joint tests along one common nontrivial filter.
It constructs the regulated continuous Schwartz extensions and the unique
full joint hierarchy. All joint tests converge along the original filter;
there is no order-dependent subsequence. The constants C(r), q(r) and m(r)
are retained exactly, so a supplied factorial bound suffers no added loss.

The input bound is genuinely support independent. A local estimate with an
arbitrary C_K for each compact K does NOT instantiate it. The input tests
are general compact JOINT tests; constructing them from source derivatives
on separate one-point tests / pure tensors is still an obligation. This
work does not assert pure-tensor density or the Fourier reconstruction
needed for that dictionary. The physical renormalized-source identity,
uniform analytic radius, actual joint bound, and actual compact-joint
convergence are still not supplied.

Verification command:

    python3 tools/verify_original30_compact_extension.py

with the pinned Lean on PATH. The local LD_PRELOAD shim only supplies
process executable-path lookup. The audit records warnings-as-errors
builds, complete untruncated theorem types, standard-foundation-only axiom
checks, five kernel replays, and recursive project dependency SHA256 values
in `verification/original30-compact-extension-20261031/summary.json`.

This is a completed concrete functional-analysis subchain, not a completed
new original manuscript environment. The conditional ledger stays 37/39;
original 24 and 30 remain open. I7 remains an explicit unproved premise.
