# Yang–Mills U–I–C: official Lean pin verification ledger — 2026-10-29

## Fixed formal toolchain
- Lean: `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`
- Formal proof check: real GitHub-hosted Lean compilation, root theorem type printing,
  `#print axioms`, `sorryAx` exclusion.
- Source manifest: original manuscript retains **39 theorem environments**.
- **This is a union of historical strict-pin receipts and new strict-pin rechecks,
  not one freshly executed 34-environment whole-repository build.**

## Audited counts (do not mix)
1. Historical + new strict-pin per-environment verified union: **34/39 = 87.18%**.
2. Standard-input-assisted conditional theorem work ledger: **34/39 = 87.18%** (unchanged
   by this recheck).
3. Lean-native conditional theorem implications: **31/39 = 79.49%** (unchanged).
4. Proven unconditional Yang–Mills U–I–C / 4D SU(2) mass-gap main theorem:
   **NO**. I7 and multiple actual Wilson input producers remain unproved.

Previously reported official-pin set (24 IDs):
`2,3,4,5,6,7,8,9,10,11,12,13,14,18,20,21,23,26,27,29,36,37,38,39`.

Newly rechecked existing conditional original environments (10 IDs):
`15,16,19,25,28,31,32,33,40,41`.

Thus current strict-pin union is
`2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,19,20,21,23,25,26,27,28,29,31,32,33,36,37,38,39,40,41`.

Still unverified original-environment IDs: **`1,24,30,34,42`**.

## New actual GitHub compilation/audit evidence
- Original32, permutation symmetry: [Actions 40864410655](https://github.com/penghongzhong/YM-closed/actions/runs/40864410655) — success.
- Original40/41, variance-to-GNS nontriviality: [Actions 40866565686](https://github.com/penghongzhong/YM-closed/actions/runs/40866565686) — success, both roots.
- Original25/31, rotation matching and Euclidean covariance: [successful job 123437474351](https://github.com/penghongzhong/YM-closed/actions/runs/40870929095/job/123437474351) (the overall matrix run failed in different jobs, not these theorem environments).
- Original33, clustering: [successful job 123439218923](https://github.com/penghongzhong/YM-closed/actions/runs/40871440518/job/123439218923) (different matrix job failed).
- Original19, counterterm cocycle: [successful job 123440183769](https://github.com/penghongzhong/YM-closed/actions/runs/40871724881/job/123440183769) (different matrix job failed).
- Original28, continuum reflection positivity: [Actions 40871884197](https://github.com/penghongzhong/YM-closed/actions/runs/40871884197) — success.
- Original15/16, full Loewner operator-order and resolvent/continuous-spectrum conditional gap: [Actions 40873357214](https://github.com/penghongzhong/YM-closed/actions/runs/40873357214) — success, both roots.
- Original30 analytic components, actual scaled dyadic shell derivative bounds, one-real-coordinate periodicization, genuine torus Fourier `C²` reconstruction:
  [Actions 40865085036](https://github.com/penghongzhong/YM-closed/actions/runs/40865085036) — success. These are **components, not Original30 completion**.

The newly rechecked exact root statements passed the pinned Lean compilation
and reported only `propext`, `Classical.choice` and `Quot.sound`;
no `sorryAx` or custom axiom is accepted.

## Proof-scope and unresolved model inputs

Original15/16: explicit I7 Gram capture/coercivity remains a theorem premise;
the `NonnegativeHeatCalculus` spectral packet/functional calculus inputs remain
explicit. In particular, a conditional theorem formally named
`original16_uniform_mass_gap_from_I7` does not prove I7 or the
unconditional Yang–Mills mass gap.

Original19: the relative source/counterterm smallness and original
normalization data are premises, not derived Wilson estimates.

Original25/31: original finite-regulator rotation/relabeling,
translation/smearing identities and joint-limit data stay visible
as hypotheses.

Original28: actual finite-cutoff reflection positivity and matching
continuum moment inputs are presumed, not manufactured by the Lean proof.

Original32: finite-cutoff analytic source map and same joint-net convergence
are hypotheses.

Original33: actual rooted-polymer counting, physical-length/tau geometry,
connected cumulant identity and same-filter limits are upstream inputs.

Original40/41: reference-root normalization, physical transfer deficit,
joint first/second moments and GNS pairing are explicit.

Original30 still needs:
- genuine joint `4r`-coordinate smooth localization and derivative chain,
  not merely the proved one-coordinate continuous periodic extension;
- actual Wilson `C²` source seminorm map and regulator/volume uniform control;
- exact source-class, smearing, scalar Fourier budget, projective-to-joint
  Schwartz/test compatibility, all-orders OS `E0'` estimate;
- full agreement with compact-test Schwinger hierarchy and common limits.

Original24 requires actual Wilson counterterm/RG source norm dictionary.
Original34 OS reconstruction depends on completed OS hypotheses.
Original42 final U–I–C assembly depends on the missing physical inputs;
Original1 UV/model input is likewise not considered closed.
I7 remains **unproved** and is **not counted**.

## Next proof effort: shortest actual completion
Prioritize Original30's physical Wilson `C²` source dictionary and
joint-periodization lemma, deriving the Fourier coefficient input directly
from actual regulated source functions, with complete root/volume/cutoff
quantifiers. Promote 34/39 to 35/39 only once an unchanged **original
manuscript environment** passes the full official-pin audit; never count
new auxiliary lemmas as original environments.
