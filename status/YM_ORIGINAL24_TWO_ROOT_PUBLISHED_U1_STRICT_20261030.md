# YM-closed — C29 Original24 genuine two-root old/new-R U1 audit (2026-10-30)

## Fixed strict work state

- Public branch `ym-original24-link-wilson-20261030`, no private Actions or changes to `main`.
- Lean `leanprover/lean4:v4.35.0-rc3`, mathlib `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
- Original manuscript conditional/theorem interface union **37/39 = 94.87%**.
- Original environments still **24 and 30**. I7 is an **UNPROVED explicit premise**, not an introduced axiom.
- Do NOT count these new strict helper/bridge theorem declarations as original24 PASS until the complete true polymer model/jet dictionary is instantiated and the paper's unchanged target statement is checked.

## Exact successful GitHub Actions receipts

1. [40996554264](https://github.com/penghongzhong/YM-closed/actions/runs/40996554264) **SUCCESS**.
   `YMOriginal/Original24_TwoExternalWilsonRoots.lean`: 4 new theorem declarations:
   actual mixed-source subtraction
   `D_p(s)D_q(t) = exp(s O_p+t O_q)-exp(s O_p)-exp(t O_q)+1`,
   genuine SU2 two-root small-source bound, rooted tree summation, and
   **sitewise local gauge invariance** for actual link-based closed Wilson loops.
2. [40998298304](https://github.com/penghongzhong/YM-closed/actions/runs/40998298304) **SUCCESS**.
   `YMOriginal/Original24_TwoRootFullRadius.lean`,
   `YMOriginal/Original24_TwoRootOldNewU1.lean`,
   `YMOriginal/Original24_FixedLinkSupport.lean`, 7 new certified declarations:
   exact full non-small source radius
   `K_{p,q}(r) = (exp(r Bp)-1)(exp(r Bq)-1)`;
   corrected two-root tree summation and simultaneous true U1 old/new R
   powers `CR*g^kappa0`, `CRnew*exp(-p0(g))`;
   actual nearest-neighbor finite-word support radius `L*a` and
   two-word support separation overhead `2*L*a`.
3. [40998329180](https://github.com/penghongzhong/YM-closed/actions/runs/40998329180) **SUCCESS**.
   `YMOriginal/Original24_FromPublishedU1ActualLinks.lean`:
   `actual_link_two_root_from_exact_published_U1` compiles and prints full
   theorem/axiom audit. This theorem inputs the exact **verbatim already audited
   Balaban U1 external theorem structure**, not a newly postulated
   `hOld` or `hNew`. Actual SU2 link-holonomy words build both external
   sources at the same anchor. The exact original public
   `Lean/Section02/T001_U1_PublishedInterface.lean` source is copied
   unchanged to `YMOriginal/Original01_U1PublishedBridge.lean` strictly
   for Lake import compatibility. The original U1 physics remains an
   **external published input**, not internally reproved.

All three official pinned workflows report **success**.
The checked declarations use only standard
`propext`, `Classical.choice`, `Quot.sound`;
`sorryAx`, `sorry`, `admit`, added `axiom` absent.

## C29 precise equation crosswalk

- §15.4–15.5: actual two *gauge-invariant* fixed-complexity Wilson roots,
  two independent complex source parameters `s,t`,
  `D_p(s)=exp(s O_p)-1`, `D_q(t)=exp(t O_q)-1`.
- (315)–(316): actual finite word budget `Bp,Bq`;
  exact full-radius bound `exp(r B)-1`.
- (317): rooted two-external-root sum controlled by
  `K_{p,q}(r) exp(mu*cRt) Nroot aAct exp(-mu*dRoot)`.
- (318)–(319): old-R `g^kappa0`, new-R `exp(-p0(g))`
  directly inherited from exact public U1 data, no R(s,t)-analytic
  deformation or small-coupling/cutoff-power exchange.
- Fixed template with at most `L` nearest-neighbor lattice edges:
  actual physical root support radius `L*a`,
  root-pair separation overhead `2 L*a`.

## Still mathematically unclosed, NOT a 38/39 claim

1. **Original24**: show the actual U1 polymers in the Yang–Mills measure,
   at the fixed D source family, satisfy **the same** rooted-history
   connectivity graph, native vs relative length dictionary,
   root-pair geometry and U2 Fernández–Procacci tree count
   `hU2Old/hU2New`, with the exact v57/CMP119/CMP122 model
   identities. The formal U1 published input alone is not this
   physical matching. Confirm B10 scale/local projection and canonical
   jet identity on the same source before lifting the entire theorem.
2. **Original30**: the verified all-volume bare Wilson source estimate
   cannot be substituted for the physical renormalized field
   with `a^(-d)` canonical normalization. Derive actual fixed-D
   source RG/jet mixing, cutoff-and-volume uniform analytic radius,
   **joint 4r test** OS E0prime bound, and same-net nontrivial
   continuum Schwinger limit. The ordinary bare Wilson bound is
   insufficient for this.
3. **I7** remains an explicit unproved premise in the conditional
   mass-gap chain; no new theorem here resolves the physical mass gap.

## Next shortest mathematical cut

Prove the exact U2 model-rooted graph/history interface from the
published U1/FP objects (NOT by assuming the desired marked sum),
then the fixed-D counterterm projection on the same actual Wilson
source. Only after the complete Original24 is verified attempt
promotion to 38/39; Original30 remains a genuinely harder interacting
RG uniform source and continuum reconstruction obligation.
