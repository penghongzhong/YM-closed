# YM Original30 — physical Wilson source, dual cocycle and geometric decay audit

Official pin: Lean 4.35.0-rc3; Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

- [Public Actions 40890284763](https://github.com/penghongzhong/YM-closed/actions/runs/40890284763): **success**, real compile, full type prints and axiom audit, no errors. 27 source-chain declarations audited, each with standard `propext`, `Classical.choice`, `Quot.sound` only. The genuine `SU(2)` root bound from `RootBound.lean` is separately audited.
- New proof modules: `YM/Wilson/DualSourceInverse21.lean`, `YM/Wilson/DualSourceRGUniform21.lean`, `YM/Wilson/SourceDefect21.lean`, `YM/Wilson/SourceGeometric21.lean`. Exact corrected source binder `∀ (n : ℕ) (β : Fin 21)` verifies **all** RG layers, not just 21 finite indices.

## New strictly proved conditional analytic estimate

For an explicit primal relative perturbation A_n on the 21-dimensional source fiber and its dual inverse-transpose B_n satisfying
`(I + A_n^T) B_n = I`, suppose
`0 ≤ θ < 1`, `0 ≤ D ≤ 1/2` and
`∀ n,β, Σ_j |A_n(β,j)| ≤ D θ^n`.
Then the actual SU(2)-plaquette-sourced **model source defined in the Lean file**
obeys for every RG layer and finite UV/volume regulator
`‖h_(f,n)‖_∞ ≤ 4 exp(2 D/(1−θ)) p_(0,0)(f)`.
The geometric series budget and inverse norm are **derived**, not supplied as additional premises.

## Model boundary: no numerator change

The manuscript's actual v111 finite-template 21-root basis, v112-v114 counterterm matrix, classical normalization, and its regulator/cutoff/volume dependent Wilson source map have not yet been identified with the abstract root-fiber matrices in this auxiliary Lean certificate. Crucially, geometric decay `Σ_j ‖A_n(β,j)‖ ≤ D θ^n` has **not** been proved from actual Wilson RG estimates. The paper's weaker per-step `‖A_n‖ ≤ 1/2` does not entail a cutoff-uniform product bound.

**Original environment verification stays 34/39**; pending original IDs remain `1,24,30,34,42`; I7 remains unproved. Do not relabel this auxiliary result as accepted Original30 or an unconditional YM mass gap.
