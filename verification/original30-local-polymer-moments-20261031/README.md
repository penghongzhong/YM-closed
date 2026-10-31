# Original 30: local-source finite-polymer cancellation

Base: `35160399f818a1b9045eda771da856d1d39178fe` (local equivalent
tree `6681519`). Lean 4.35.0-rc3, Mathlib
`516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.

`YMUIC.Original30.local_polymer_source_normalized_moments` takes a finite
polymer set and an active predicate. On the source ball `ball 0 ρ` it assumes
that the activity of every inactive polymer is independent of the source;
only active activities are required to be analytic and subject to weights
whose sum is at most `A`. It derives exact cancellation of the inactive
terms in the normalized finite source, equality of the full and active-source
iterated derivatives at zero, and the same all-order moment estimate as
`polymer_source_normalized_moments`. The proof needs no all-volume bound on
the total unnormalized background activity and imposes no assertion about
source values outside that ball.

Actual Wilson/RG source locality, the source-support identification,
the active weight budget uniform in volume and cutoff, the joint Schwartz
dictionary and the continuum limit remain unproved model obligations. This
conditional lemma does not accept Original 30 or establish physical YM
regularity. The 37/39 conditional original-environment ledger is unchanged.

Verification with the pinned toolchain and Mathlib cache:

- `lake build YMOriginal.Original30_LocalSourcePolymerMoments`: exit 0;
  the Lake target used `-DwarningAsError=true`.
- `lake env lean -DwarningAsError=true verification/original30-local-polymer-moments-20261031/ExactType.lean`:
  exit 0; full type and transitive axiom audit in `exact-type-axioms.log`.
- `lake env leanchecker -v YMOriginal.Original30_LocalSourcePolymerMoments`:
  exit 0; replay record in `kernel-replay.log`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or
  new axioms. Source SHA-256:
  `2bcd515396065a2ea138e953c8cb3920317be46959de9bc841d0f3b5101eb51f`.
