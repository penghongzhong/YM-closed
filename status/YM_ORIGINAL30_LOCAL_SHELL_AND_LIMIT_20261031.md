# Original 30: local activity, shell budget, OS zero-order and common-filter bridges

Baseline: remote commit 35160399f818a1b9045eda771da856d1d39178fe
(the same tree as local commit 6681519). Official Lean 4.35.0-rc3 and
Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

## Verified components

1. `local_polymer_source_normalized_moments`: if inactive finite-volume
   polymer activities are source-independent on the source ball, they
   cancel exactly in the normalized generating function and all its
   derivatives; only active activities need analytic bounds and a budget.
2. `local_source_moments_from_shell_count`: if active activities have
   the stated exponential bound and shell counts, their budget is derived
   as A = epsilon C/(1-exp(-(kappa-sigma))), not assumed independently.
   Applying 1 gives all normalized moments with polynomial dependence on A.
3. `bare_joint_os_radial_zero_bound`: for the bare joint Wilson moment,
   the explicit Schwartz supremum M_r(f)=sup_x (1+||x||^2)^(4r)||f(x)||
   is finite and yields the uniform bound 2 exp(24576 K) r! M_r(f).
   M_r is the alpha=0 term of the OS 1975 (2.1) norm with index 8r.
   This is not a proof for the renormalized model, nor a proof of E0''.
4. `joint_same_filter_limit`: under convergence of the joint regulated
   functionals on each test and a uniform joint seminorm bound on the same
   nontrivial filter, the limit is constructed as a continuous linear
   joint-test hierarchy and retains the bound. Convergence and its
   identification with the physical model remain hypotheses.

Each source module passed target Lean compilation, complete type/axiom
inspection and leanchecker replay. See the four corresponding directories
under verification/ for exact statements and execution records; only
propext, Classical.choice and Quot.sound occur. No original manuscript
environment was completed by these conditional bridges.

## Remaining model obligations

Construct the actual source-deformed renormalized activities and prove their
locality, uniform analytic radius, decay and rooted count with constants
independent of regulators. Produce the normalized source/test dictionary
and the genuinely joint Schwartz bounds and common physical continuum net.
The original v133 C1 estimates are quantified after fixing r and cannot alone
provide the uniform all-order radius and constants claimed in B13. Also,
local support-dependent bounds alone do not establish temperedness.

Conditional original-environment ledger remains 37/39; original 24 and 30
remain open and I7 is retained as an explicit unproved premise.
