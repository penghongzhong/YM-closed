# YM Original32: actual permutation symmetry — official Lean pin

This public branch reproduces exactly two Lean source blobs from the existing
conditional proof of C29 original environment 32, Lemma 17.7 (Schwinger
permutation symmetry, Eq. 351).

- The theorem **derives** symmetry of the source Frechet derivatives from
  `AnalyticAt`, then transfers that equality over the *same joint* cutoff-volume
  net using `Tendsto` uniqueness.
- The necessary *actual-model hypotheses* `hanalytic`, `liftSource` and
  `hjoint` are **explicit inputs**. Neither finite Wilson source analyticity
  nor joint convergence is established anew by this module.
- This theorem does not depend on I7 and is not a proof of the Yang–Mills mass
  gap, and cannot be counted as a new 34/39 conditional-environment acceptance.

**Acceptance criterion:** exact Lean 4.35.0-rc3 / Mathlib
`516d31250e96c4e8e76888c3d8e2e43a9642b9ee`, successful build, full
theorem-type output and `#print axioms` audit with no `sorryAx`/custom axioms.

If accepted, this is an *official-pin reconfirmation* of previously counted
conditional environment 32, not a 35th new conditional environment.
