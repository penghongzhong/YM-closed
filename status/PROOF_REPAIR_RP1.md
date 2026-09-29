# RP1 proof-repair certification

Date: 2026-09-29. Certified Lean source commit: `8e14ed24b86d16de87192166b4c5976464898b71`.

## Verified evidence

- Fast run #44: `36509839892`; job `109219360327`.
- Full repository run #44: `36509839844`; job `109219378656`.
- Both jobs completed SUCCESS. Raw logs were inspected, not only the UI conclusion.
- Fast final gate: `2026-09-29T01:55:14.1990486Z FINAL_GATE=SUCCESS`.
- Full final gate: `2026-09-29T01:57:10.5817913Z FINAL_GATE=SUCCESS`.
- Each file below has raw exit code 0, and each listed theorem has a printed axiom audit using only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
- The source and privacy scans report `source_violations=[]`, `private_paths=[]`.

| File under Lean/Repair/ | Theorems | Exact certified scope | Status |
|---|---:|---|---|
| T013A_FiniteMetropolisEnergy.lean | 4 | Finite stationary-flux energy and Metropolis flux bookkeeping | INTERNAL HELPER PASS |
| T013B_UnitaryRectangleTelescoping.lean | 3 | Four-edge linear/isometric identity and squared norm estimate | INTERNAL HELPER PASS |
| T013C_QuaternionCommutator.lean | 4 | Explicit quaternion coordinate commutator, norm and axis average | INTERNAL HELPER PASS |
| T013D_NoncentralCurvatureCertificate.lean | 4 | Nonnegative polynomial certificate and finite coherent weighted inequality | INTERNAL HELPER PASS |
| T013E_SlabScoreCompression.lean | 4 | Hilbert-space compression correction and scalar diagnostic | INTERNAL HELPER PASS |
| T013F_FreshLinkCaptureArithmetic.lean | 6 | Rotation-average polynomial, capture threshold and constant arithmetic | INTERNAL HELPER PASS |

Total: 6 files, 25 printed theorem certificates. Existing source files are unchanged except for the RP1 additions; the full run supplies their regression check.

## Mathematical boundary

The private RP1 manuscript proves the continuous correlated-measure rectangle estimate, the explicit noncentral ordered-word coefficient Gram inequality, and fresh-original-link capture under an explicit activity threshold. The Lean files certify the finite/Hilbert/polynomial sublemmas above, NOT the entire continuous conditional-measure derivation end to end.

The coefficient Gram is NOT identified with the physical Wilson transfer deficit. Actual registered-source membership, same-state same-physical-window payment, and coverage of the remaining word/peak/outward/off-cycle branches are not proved. I7-GLOBAL-ROOT-FRAME remains OPEN. No unconditional UIC closure is certified.

The slab-to-slice repair retains the conditional-projection residual. Its pairing is not generally zero, as an exact two-time Wilson-factor diagnostic shows. This diagnostic is not a counterexample to the four-dimensional Yang--Mills gap.

See `I7_REPAIR_OBLIGATIONS.md` for the precise remaining interfaces and `RP1_CI_EVIDENCE.json` for machine-readable run provenance.

Privacy: this repository contains Lean, verification tools and ledgers only. The private current manuscript and its PDF are synchronized in /YM, never in this repository. Lean/mathlib pins are unchanged.
