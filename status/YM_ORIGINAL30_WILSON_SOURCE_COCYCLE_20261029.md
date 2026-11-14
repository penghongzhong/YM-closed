# YM-UIC Original30: actual Wilson SU(2) source and RG cocycle — 2026-10-29

## Fixed toolchain and actual GitHub receipts

Repository: `penghongzhong/YM-closed` (public).
Isolated branch: `ym-original30-wilson-source-20261029`.
Lean: `leanprover/lean4:v4.35.0-rc3`;
Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.

Three GitHub-hosted runner executions, all success, performed strict compilation,
theorem type printing and `#print axioms`:
- [40880198737](https://github.com/penghongzhong/YM-closed/actions/runs/40880198737):
  1 inherited original SU2 Wilson-root theorem and 8 concrete root/source theorems.
- [40880896848](https://github.com/penghongzhong/YM-closed/actions/runs/40880896848):
  3 additional exact 21-dimensional source-cocycle composition/matrix column estimates.
- [40882672688](https://github.com/penghongzhong/YM-closed/actions/runs/40882672688):
  4 additional finite and all-level RG cocycle estimates.

The source modules are:
- `YM/Wilson/RootBound.lean` (exact copied root theorem, no custom axiom);
- `YM/Wilson/SourceDirection.lean` (5 new theorems);
- `YM/Wilson/SourceMix21.lean` (3 new theorems);
- `YM/Wilson/SourceCocycle21.lean` (3 new theorems);
- `YM/Wilson/SourceCocycleChain21.lean` (4 new theorems).

All 15 new declarations passed under the pin with only the foundations
`propext, Classical.choice, Quot.sound`. In particular no `sorryAx`,
new axiom, or circular theorem assumption was used.

## Proved mathematical results

For every finite set of genuine `SU(2)` plaquette holonomies `U_p`,
and arbitrary physical plaquette positions `x_p ∈ ℝ⁴`, put

`W_p(U)=2-Re Tr(U_p)`, `h_f(p)=W_p(U) f(x_p)`.

Then for every Schwartz test `f ∈ 𝓢(ℝ⁴,ℂ)`:

`0 ≤ W_p ≤ 4`, `‖h_f‖_{ℓ∞} ≤ 4 p_{0,0}(f)`.

No factor depending on the number of plaquettes, lattice spacing, position or
volume appears. The difference of source tests is bounded by
`‖h_f-h_g‖_{ℓ∞} ≤ 4 p_{0,0}(f-g)`.

For **21** such plaquette-root directions, define

`h_{B,f}(α)=∑_{j=1}^{21} B_{jα} h_f(j)`.

The exactly proved matrix/source inequalities are:

`‖h_{B,f}‖∞ ≤ 4 (max_α ∑_j |B_{jα}|) p_{0,0}(f)`
(with the RHS in Lean expressed through a universal column-sum bound).

For two source basis changes the actual matrix action composes exactly,
and its column `ℓ¹` amplification is submultiplicative.

Define `Z_0=I` and `Z_{m+1}=Z_m C_m`. If

`∀j,α: ∑_k|C_j(k,α)| ≤ 1+δ_j`, `δ_j≥0`,
and `∀m: ∑_{j<m}δ_j ≤ M`,

then Lean derives

`∀m: ∑_k |Z_m(k,α)| ≤ ∏_{j<m}(1+δ_j) ≤ exp M`

and hence

`∀m: ‖h_{Z_m,f}‖∞ ≤ 4 exp(M) p_{0,0}(f)`.

**The cumulative `Z_m` operator bound is proved from per-step inputs,
not separately assumed.**

## The critical missing genuine RG input

The user's C29 §14 equations (297)–(305) construct one-step source matrices
`M_{j,D}=M_D^(0)(I+A_{j,D})` and a cumulative cocycle `Z_{m,D}`,
with the dual source coordinates `Jhat=Z_{m,D}^{-T}J_0`.
The paper's single-step `‖A_{j,D}‖≤1/2` yields
`‖(I+A_{j,D})^{-1}‖≤2` but **does not imply a cutoff-uniform
bound for the cumulative inverse**. For instance `I+A_j=I/2` gives
`‖Z_m^{-1}‖=2^m` when the classical factor is identity.

Thus one must:
1. identify the actual source-step matrix in the correct **dual/inverse
   transpose** canonical coordinates and prove its quantitative
   `21×21` column amplification, or a compensation/cancellation bound;
2. establish a cutoff-uniform summability estimate for its step errors
   `δ_{j,D}` (if available), rather than infer it from one-step smallness;
3. relate the actual 21 **fixed-template curvature/Wilson-word roots** to the
   formal 21 plaquette-root family used by this module, preserving coefficients,
   source normalization, engineering dimension, support and derivatives;
4. match v108/v118 normalized smearing/source freezing, volume/cutoff
   convergence, polymer source chart and the joint 4r-coordinate
   Schwartz/Fourier coefficient estimate to the OS `E0′` hypothesis;
5. retain the unresolved I7 and original environments 1,24,30,34,42.

The source theorem is **about genuine SU2 plaquette roots**, but it has not
shown that the 21 specific renormalized polynomial roots of the
manuscript equal those 21 plaquette directions or that the source
matrices satisfy the hypothesized step summability. Those statements
must not be silently substituted.

## Accounting

- Previously compiled strict-pin original-environment union: **34/39**, unchanged.
- Conditional original-environment work ledger: **34/39**, unchanged.
- Lean-native conditional original-environment set: **31/39**, unchanged.
- New current-turn actual Wilson source/cocycle Lean theorem declarations: **15**,
  all verified, not original manuscript environments.
- Unconditional Yang–Mills existence/mass gap: **NOT proved**; I7 unproved.

Next strict task: formalize the actual fixed-21-root polynomial observable
source dictionary and obtain the quantitative cumulative inverse-transpose
RG cocycle bound without introducing a theorem parameter that simply states
the desired global OS-growth conclusion. The original 30 can only be counted
if all original hypotheses are genuinely verified.
