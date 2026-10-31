Target YMUIC.Original30.bare_joint_linear_weight_factorial_bound
Base efa6f887167ac59a4d23a6e3997f556ad5f50c84
Lean 4.35.0-rc3, Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.
Commands (from the base worktree with the pinned toolchain on PATH and LD_PRELOAD=/tmp/ym-lean/proc-self.so):
  lake build YMOriginal.Original30_BareLinearGrowthCertificate -- exit 0
  lake env lean -DwarningAsError=true /tmp/ym-linear-growth-audit/Exact.lean -- exit 0; exact.log
  lake env leanchecker -v YMOriginal.Original30_BareLinearGrowthCertificate -- exit 0; kernel.log
The complete type log has no truncation marker or sorryAx. Axioms: propext, Classical.choice, Quot.sound.
Result: the actual bare Wilson joint probability moment is integrable and bounded by 2 exp(24576 K) r! jointSchwartzControl r (8r) (8r), uniformly in cutoff and volume, assuming the existing true-Wilson polynomial coefficient budget K and measurability.
This is not an OS norm equivalence, not renormalized-source matching, not a common continuum limit and not a complete Original30 acceptance. The conditional original-environment ledger remains 37/39.
