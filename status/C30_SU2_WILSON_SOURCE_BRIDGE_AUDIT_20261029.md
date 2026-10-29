# Original30 actual SU(2) Wilson-to-Schwartz source bridge — verified 2026-10-29

This note records **actual fixed-pin Lean proof output**, not proposed
analysis and not a completion of Original30.

## Verification settings

- Public repository: `penghongzhong/YM-closed`.
- Isolated branch: `ym-c30-wilson-source-20261029`; `main` unchanged.
- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
- Every new source target was compiled and its full type / `#print axioms`
  audited. Axiom output: `propext`, `Classical.choice`, `Quot.sound`;
  no `sorryAx` or novel axiom.

## New accepted proof chain (12 exact theorem declarations)

1. [Run 40877242949 — SUCCESS](https://github.com/penghongzhong/YM-closed/actions/runs/40877242949):
   `WilsonPlaquetteSmearing.lean` — 3 new theorems `wilsonPlaquetteSchwartz_term_bound`,
   `wilsonPlaquetteSchwartz_finite_bound`,
   `wilsonPlaquetteSchwartz_uniform_bound`.
   The actual `SU2` root formula `W_p=2-Re Tr(U_p)` and `0≤W_p≤4`
   come from unchanged, already kernel-proved public code
   `YM/Wilson/RootBound.lean`.
2. [Run 40878186138 — SUCCESS](https://github.com/penghongzhong/YM-closed/actions/runs/40878186138):
   `WilsonHypercubicPacking.lean` — 3 new theorems
   `periodic4D_plaquette_card`,
   `periodic4D_physical_plaquette_count`,
   `periodic4D_wilson_Schwartz_uniform`.
   The 4D periodic regulator has precisely six unoriented plaquette
   orientations and `N⁴` sites, hence `#S≤6N⁴`. If `aN≤L`,
   then `|J(f)|≤24L⁴p₀,₀(f)`, with no arbitrary counting premise.
3. [Run 40879092650 — SUCCESS](https://github.com/penghongzhong/YM-closed/actions/runs/40879092650):
   `WilsonSchwartzCLM.lean` — 4 new theorems
   `wilsonPlaquetteSchwartzCLM_apply`,
   `wilsonPlaquetteSchwartzCLM_add`,
   `wilsonPlaquetteSchwartzCLM_smul`,
   `periodic4D_wilson_SchwartzCLM_uniform`.
   A genuine Schwartz continuous complex-linear map is assembled from
   Mathlib's Dirac evaluation CLMs, and is proved pointwise equal to the
   original `a⁴ Σ_{p∈S} (2-Re Tr U_p)f(x_p)` source.
4. [Run 40880090464 — SUCCESS](https://github.com/penghongzhong/YM-closed/actions/runs/40880090464):
   `WilsonLocalChart.lean` — 2 new theorems
   `localPlaquette_card_from_chart` and
   `localPlaquette_SchwartzCLM_uniform`.
   Assuming an explicit injective support-chart encoding
   `{p : globalPlaquette // p∈S} ↪ Periodic4DPlaquette M` and a
   **fixed local** physical size `aM≤R`, Lean proves
   `|J(f)|≤24R⁴p₀,₀(f)`, independent of the number of sites and
   the physical length of the *global* regulator.

## Scope and genuine remaining mathematical obligations

- These are **12 new load-bearing *auxiliary* theorems**; not twelve
  of the 39 retained manuscript environments.
- Official-pin original-environment verified union remains **34/39**,
  standard-input-assisted conditional count remains **34/39**,
  native conditional count remains **31/39**.
- Pending original manuscript IDs: **1,24,30,34,42**.
- I7 remains **UNPROVED**. The Yang–Mills mass gap and U–I–C main
  theorem are **not** unconditionally proved.
- The source constructed here is the finite *unrenormalized* Wilson
  plaquette test functional. No RG-connected polymer source expansion,
  root-to-chart compatibility, or actual regulator-uniform connected
  moment/factorial hierarchy has been constructed from it.
- In the local bound, **the existence of the chart injection is a
  separate premise**, not proved from arbitrary support positions.
  This is a precise geometry dictionary still to instantiate for
  the actual Wilson test supports; the estimate is not a full
  infinite-volume convergence result.
- To certify Original30 one must construct the actual *renormalized
  connected Wilson* source maps; prove the uniform localized C²
  source seminorm dictionary and joint `4r`-coordinate Schwartz
  periodization; establish scalar Fourier tensor coefficient budget,
  projective-to-joint compatibility and exact OS E0′ growth;
  match the original paper's all-orders hypotheses and filters.

**Next exact proof target:** actual coordinate/support localization of
the Wilson cylinder source into the chart (remove the `encode`
premise), then local source-norm control for connected RG polymer
derivatives. Never promote to 35/39 before the complete Original30
manuscript theorem environment passes full exact-pin verification.
