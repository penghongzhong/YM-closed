# C29 Original30: strict public Wilson-source smearing continuation (2026-10-29)

## Exact pinned Lean evidence

- GitHub [#40888984334](https://github.com/penghongzhong/YM-closed/actions/runs/40888984334):
  **success**, actual SU(2) plaquette-source and weighted Schwartz smearing.
  Code: `YM/Wilson/WeightedSmearing.lean`.
  Four strict theorems: `schwartz_weighted_point_bound`,
  `wilson_weighted_point_bound`, `wilson_weighted_smearing_bound`,
  `wilson_weighted_smearing_all_regulators`.
- GitHub [#40890294365](https://github.com/penghongzhong/YM-closed/actions/runs/40890294365):
  **success**, actual 4D periodic fixed-physical-box count and source
  normalization. Code: `YM/Wilson/FixedBoxSmearing.lean`.
  Three strict theorems: `wilson_box_weighted_sum_bound`,
  `wilson_box_source_bound`,
  `wilson_box_source_uniform_across_cutoffs`.
- Lean: `4.35.0-rc3`; Mathlib:
  `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
  Compiler, statement rendering and `#print axioms` checks: success,
  standard `propext`, `Classical.choice`, `Quot.sound` only;
  no `sorryAx` and no new axiom.

## Genuine mathematical statements

For actual root `W_p(U)=2-Re Tr U_p`, `U_p∈SU(2)`, and a complex
Schwartz test `f∈𝒮(ℝ⁴)`, the **defined** finite weighted source

`S_P(f,U)=∑_{p∈P}w_p f(x_p) W_p(U)`

satisfies for any `q∈ℕ`:

`|S_P(f,U)| ≤ 4 [∑_p |w_p|/(1+‖x_p‖^q)] [p_(0,0)(f)+p_(q,0)(f)]`.

This is derived from actual `SchwartzMap` seminorms and the SU(2)
Wilson root bound.  No source continuity hypothesis is assumed.

For the canonical **six** unoriented positive plaquette types at each site
of a 4D periodic N-by-N-by-N-by-N lattice, let

`P_N=Fin 6 × Fin (N^4)`, `w_p=a^4`, `a≥0`, `R≥0`, `N a ≤ R`.

Then *without any a-dependent geometric input*,

`∑_(p∈P_N) a^4/(1+‖x_p‖^q) ≤ 6R^4`,

and hence

`|S_(N,a)(f,U)| ≤ 24R^4 [p_(0,0)(f)+p_(q,0)(f)]`.

The same constant works for every regulator with the same fixed physical
box size R, arbitrary SU(2) plaquette configuration and sample positions.

## Red nodes retained: do not count this as full Original30

1. This is a **bare a⁴-weighted root sum**. The actual normalized and
   renormalized engineering-dimension D=4 Wilson composite source in v108/v118
   may have different canonical a-weights, field/counterterm mixing,
   local jet subtraction and RG source cocycles. An unproved model matching
   cannot be inferred from a bare plaquette bound.
2. The bound grows like `R⁴`: it is not an infinite-physical-volume
   Schwartz/OS `E0′` distribution bound with one global uniform constant.
   The exact *physical* weights must satisfy the volume-uniform weighted
   quadrature condition, not merely the chosen bare `a⁴` weights.
3. The source transformation is the **dual inverse transpose**
   `Ĵ=Z^{-T}J`, not the primal matrix. Uniform amplification or
   an exact local-jet cancellation/remainder decomposition is still required
   and must follow from genuine B09–B11 model estimates.
4. Actual joint `4r` smooth periodization and Fourier factorization,
   Wilson source dictionary, OS `E0′` growth, OS reconstruction and I7 remain open.

## Honest proof ledger

- Historical + new official-pin **conditional** environment union: **34/39**.
- Standard-input-assisted conditional manuscript ledger: **34/39**.
- Lean-native conditional core: **31/39**.
- Pending original IDs: **1,24,30,34,42**.
- I7: **unproved**. No unconditional 4D SU(2) Yang–Mills mass gap.

These 7 verified Lean declarations are substantive **components of
Original30**, not a 35th verified original manuscript environment.

## Shortest next model producer

Establish (not postulate) the true normalized v108/v118 source dictionary
`f ↦ w_(a,Λ,p) f(x_p) W_p(U)` including canonical dimension and local jet,
then obtain

`sup_(a,Λ)∑_p |w_(a,Λ,p)|/(1+‖x_p‖^q) ≤ C_q`

(or a regulator-uniform source norm obtained by proven dual jet cancellation),
and combine it with the already verified Fourier/Schwartz projective
coefficient construction. Do not replace this step by a bare plaquette bound.
