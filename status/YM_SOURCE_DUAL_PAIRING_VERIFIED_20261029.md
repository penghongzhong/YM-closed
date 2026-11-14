# YM-closed: verified C29 source continuation (2026-10-29)

## Strict GitHub receipts and lock

- Official Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
- Successful all-D source pairing + repaired Nat-indexed dual RG:
  https://github.com/penghongzhong/YM-closed/actions/runs/40891267234
- Successful compensated RG frame and noncommutative Wilson words (and above):
  https://github.com/penghongzhong/YM-closed/actions/runs/40892583762
- Source branch: `ym-original30-compensated-frame-20261029`.
- Every counted auxiliary declaration: real Lean file compilation, printed full
  theorem signatures, `#print axioms`, no `sorryAx` or custom axiom.

## Eight new certified, non-manuscript auxiliary theorems

1. `source_primal_dual_pairing_allD`:
   exact source equation `Zᵀ B = I` -> `(Zv)ᵀ(BJ)=vᵀJ`,
   all finite source dimensions, no assumed cumulative operator-norm bound.
2. `paired_wilson_source_uniform_without_cocycle_norm`:
   genuine SU2 bare plaquette test pairing bounded by
   `4‖J‖_{ℓ¹} p_{0,0}(f)`; does NOT require bounds on `Z` or `B`.
3. `compensated_source_chain_factorization`:
   if `C_n=F_n R_n F_{n+1}^{-1}` with explicit exact inverse-frame
   identities, then `C_0⋯C_{m-1}=F_0(R_0⋯R_{m-1})F_m^{-1}`.
4. `compensated_source_chain_uniform_column`: follows from *summable
   residual* `R_n-I` defects and **endpoint** norms of `F_0,F_m^{-1}`;
   neither residual summability nor physical endpoint bounds are derived.
5. `compensated_wilson_source_uniform`: conditional SU2 Wilson-source
   estimate using item 4.
6. `wilson_word_root_bounds`: ordered (noncommutative) SU2 word holonomy
   `U_{p1}⋯U_{pk}` has bounded `W=2-ReTr(U_word)∈[0,4]`,
   irrespective of word length and lattice regulator.
7. `wilson_word_combination_bound`: any fixed finite coefficient sum of
   genuine SU2 Wilson words has `norm ≤ 4 Σ‖coeff‖`.
8. `wilson_word_schwartz_source_bound`: multiply item 7 by the genuine
   evaluation `f(x)`, obtaining `4(Σ‖coeff‖)p_{0,0}(f)`.

The older `DualSourceRGUniform21.lean` also compiles now after fixing BOTH
`hrow` binders from `∀ n β : Fin 21` to
`∀ (n : ℕ) (β : Fin 21)`.
Its **two existing** exact inverse-transpose source statements passed in
the same strict official-pin audit; they are not counted among the eight
new declarations.

## Critical manuscript scope separation

- Frozen original manuscript strict-pin historical union: **34/39**.
- Open ORIGINAL environment IDs: **1,24,30,34,42**.
- **No** unconditional 4D SU(2) continuum YM mass gap / UIC proof.
- I7 global interacting-measure Gram frame: **open**.
- The 21-dimensional code models a fixed finite family; the manuscript
  itself defines a dimension-`D` source space of dimension `N_D` and
  fixed-template composite Wilson roots.  The new all-D pairing lemma
  is truly dimension-agnostic, but its model-side `Zᵀ B = I` input
  must be tied to the physical RG cocycle.
- `WordSource.lean` covers **linear combinations of ordered SU2 Wilson
  words**.  Products of multiple word characters and all classical jet,
  derivative, engineering-dimension and normalization factors require
  separate source-dictionary proofs.
- The compensated frame lemma is conditional; it only relocates the model
  bound to residual step summability and endpoint frames. It should NOT
  be presented as deriving the actual RG bounds.
- Exact bilinear pairing avoids cumulative norms only in the canonical
  paired observable, **not** in the unpaired renormalized source nor the
  all-orders OS E0' analytic radius.

## The shortest next ORIGINAL30 carrying chain

1. Define the actual v111 21 fixed-template SU2 Wilson-word *products*,
   their physical smearing/quadrature normalization and the precise
   finite-dimensional `Z_{m,D}^{-T}` source dictionary.
2. Prove for this actual normalized pairing a regulator/volume-uniform
   bounded map from Schwartz tests into the source chart, preserving the
   true engineering scaling and derivatives through second order.
3. Prove the physical polymer source chart analytic radius and its
   Cauchy-derived cumulant budget for every order r, with exact
   regulator/volume quantifiers. The generic bare Wilson bound is not
   enough.
4. Establish the joint 4r-variable Schwartz/Fourier coefficient and
   projective/test compatibility, with same-filter continuum limits,
   then precisely match Original30's E0' factorial distribution bound.
5. Count **35/39** only after the unchanged Original30 statement,
   not another auxiliary theorem, passes its full official-pin audit.
   Original34/42 and I7 remain separate.

Historical original theorem counts are not altered by this continuation.
