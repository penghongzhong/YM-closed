# YM-closed original 24/30/34 proof continuation — 2026-10-30

## Strict verified count (unchanged)

- Manuscript historical *conditional original-environment* strict-pin union: **36/39 = 92.31%**.
- I7 stays a visible theorem hypothesis. It is **NOT proved**.
- Still unverified original manuscript IDs: **24, 30, 34**.
- This is NOT 36 physical Yang–Mills unconditional model theorems, and not
  a monolithic 36-original-environment build.
- Fixed Lean: `leanprover/lean4:v4.35.0-rc3`.
- Fixed Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.

## Certified additional internal supporting results

1. C29 old/new R single actual composite SU2 root:
   [Actions 40957221065](https://github.com/penghongzhong/YM-closed/actions/runs/40957221065),
   SUCCESS. `Original24_MarkedRootBridge.lean`: one-root U2 tree sum,
   actual composite SU2 root insertion × UNMARKED R, simultaneous old/new
   marked rooted bounds.
2. C29 fifth-order post-R geometric summability:
   [Actions 40957858447](https://github.com/penghongzhong/YM-closed/actions/runs/40957858447),
   SUCCESS. `Original24_PostRLocalization.lean`: prove that a separately
   recorded B10 fifth-order Taylor/placement estimate plus the derived
   marked source bound yields a summable residual tail `B/(1-q)`, `q<1`.
3. **All finite Wilson words, not only the independent 21-Gram candidate**:
   [Actions 40958204467](https://github.com/penghongzhong/YM-closed/actions/runs/40958204467),
   SUCCESS. Exact `WordSource` SU2 holonomies (including genuinely ordered,
   noncommuting words), arbitrary fixed finite word products, exact
   coefficient/length budget, complex source insertion, old/new rooted
   bounds, and B10 sum.
4. Corrected OS II published-input application:
   [Actions 40957287988](https://github.com/penghongzhong/YM-closed/actions/runs/40957287988),
   SUCCESS. `Original34_OSII_ExternalInterface.lean`. Uses the corrected
   Osterwalder–Schrader 1975 E0' + E1--E4 -> R0'--R5 theorem as an EXPLICIT
   external theorem interface. E0' is typed on genuine *joint*
   SchwartzMap(EuclideanSpace ℝ (Fin (4*r))) test functions with
   factorial and derivative-order-linear seminorm control; merely
   knowing factorized pure-test bounds does not discharge this.
   The external theorem and an arbitrary geometry registry have not been
   instantiated from the actual continuum Yang–Mills Schwinger tower.

Successful audited sources report only standard foundations
`propext, Classical.choice, Quot.sound`, without `sorryAx` or newly
declared axioms.

## New verified U1-to-U2 physical geometry bridge

- [Actions 40958732919](https://github.com/penghongzhong/YM-closed/actions/runs/40958732919)
  **SUCCESS**; `Original24_UnmarkedRGGeometry.lean`, two newly audited
  theorems: from the explicit physical-native distance dictionary
  `dRoot <= cRt + cGeo*length(γ)` and the actual UNMARKED sector
  bound `norm(z γ) <= A exp(-kappa*length(γ))`, derive the weighted
  tree exponential with `kappa-mu*cGeo`. Then apply the actual
  finite Wilson-word source theorem. No separate marked-R bound is assumed.
- The old/new R *model-specific* native distance dictionary and rooted-tree
  total summability still need actual source verification.

## Latest pending exact four-dimensional placement certificate

- `Original24_PlacementRatio.lean` states the true C29 equality
  `L^(4m) * L^(-(5-theta)m) = (L^(-(1-theta)))^m` and proves
  `0 < q < 1` directly from `L>1, 0<theta<1`.
  Await successful official-pin run before declaring it certified.

## Exact mathematical open obligations

Original24:
1. Prove the actual old/new R-sector *unmarked* native history bounds and
   root-distance/length dictionary at every cutoff and volume, with correct
   relative-versus-ordinary length distinction.
2. Match the actual fixed-D gauge-invariant Wilson source templates
   including supports, normalization and engineering dimensions to the
   arbitrary finite-word polynomial grammar.
3. Instantiate the previously certified U2 rooted-tree bound and B10
   fifth-order Taylor localization on the *same* physical source and
   history space; prove the actual q = L^(-(1-theta)) factor.
4. Then check the UNCHANGED Original24 manuscript conclusion as a true
   exact environment, not an abstract hB10 assumption disguised as an output.

Original30:
- Derive physical all-order source chart control, 4r-coordinate periodic
  smooth Fourier reconstruction, the full Schwartz/test projective
  compatibility, same-net continuum limits and OS E0' from actual
  Yang–Mills polymer/RG data. The 21-Gram independent candidate is
  NOT the missing archived v111 source and cannot silently substitute it.

Original34:
- Apply the published OS-II interface to the true renormalized continuum
  Schwinger hierarchy only AFTER E0' and all E1--E4 model hypotheses
  have been established. A conditional published theorem use alone is
  not a new proof of the physical YM reconstruction.

## LEAP guardrails

No conclusion in Original24/30/34 is silently promoted to PASS by
inventing a source norm, physical RG residual, all-order OS growth,
native root-distance dictionary or continuum reconstruction hypothesis.
Count remains 36/39 until an unchanged manuscript theorem environment
is truly checked at the declared proof scope.
