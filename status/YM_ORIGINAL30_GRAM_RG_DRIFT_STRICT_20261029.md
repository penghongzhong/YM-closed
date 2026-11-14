# YM-closed C29 Original30: source-algebra strict Lean continuation (29 October 2026)

## Official fixed-pin evidence

Repository: `penghongzhong/YM-closed`, isolated feature branch
`ym-original30-compensated-frame-20261029`; the default main branch is unchanged.

- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`.
- Candidate bare SU2 21 Gram-root dictionary (6 new theorems):
  [40894675126](https://github.com/penghongzhong/YM-closed/actions/runs/40894675126) SUCCESS.
- Finite composite Gram-root products and source budgets (5 new theorems):
  [40895207961](https://github.com/penghongzhong/YM-closed/actions/runs/40895207961) SUCCESS.
- **Original C29 left-ordered** RG canonical source action and paired source
  (4 new theorems):
  [40896506709](https://github.com/penghongzhong/YM-closed/actions/runs/40896506709) SUCCESS.
- Exact bounded complex exponential insertion of actual Gram-root polynomial
  (2 new theorems):
  [40896541621](https://github.com/penghongzhong/YM-closed/actions/runs/40896541621) SUCCESS.
- Final consolidated dependencies and all types/axioms:
  [40901943102](https://github.com/penghongzhong/YM-closed/actions/runs/40901943102) SUCCESS;
  **8995 Lake build jobs** completed, compilation of all relevant source
  modules, full theorem statements and `#print axioms` for 46 declared
  named roots/auxiliaries (some inherited, not 46 newly constructed).
  Among newly introduced THIS continuation (not inherited), 11 additional
  auxiliary theorems in Gram trace / composite paired sources / two
  finite-horizon RG drift modules, plus 3 U3 arithmetic declarations
  re-ported from previously checked manuscript helper modules.
  Overall **28 newly introduced** theorem declarations certified this turn,
  plus **3 existing U3 declarations** ported and freshly checked.
- No new `axiom`, `sorry`, `admit`, or `sorryAx` in the accepted module
  closure. `#print axioms` lists only `propext`,
  `Classical.choice`, `Quot.sound` (with universe parameters).

## Actual finite SU(2) candidate roots and products

For six genuine shared-basepoint SU(2) plaquette holonomies U_i,
let W(U) = 2 - Re Tr U. The 21 independent **candidate**
upper-triangular coordinates are
  R_ij = [W(U_i U_j) - W(U_i) - W(U_j)] / 2
       = -Re Tr[(U_i-I)(U_j-I)]/2, 1<=i<=j<=6.
The *exact matrix-trace equality* was strictly compiled and audited
in `YM/Wilson/CandidateGramTrace21.lean`.
The Gram-root bound `abs(R_ij)<=4`, finite polynomial coefficient
budget `sum_t norm(c_t) * 4^(degree_t)`, Schwartz source bound,
and a complex exponential source insertion bound on
`norm(s)*budget<=1` all passed.

**PROVENANCE WARNING**: this explicit candidate comes from an
independent 21-root reconstruction (25 October 2026), *not*
the still-missing original v111 C-stage PDF/TEX. We have NOT proved that
this candidate matches the historical 21 fixed templates, the
engineering normalizations or canonical jet matrix of the original
manuscript. Its physical local-continuum `a^{-4}` curvature expansion
and exact `T_4=I_21` have not been Lean verified.

## Paper-ordered RG and new precise conditional estimate

C29 §14 original equation (304):
  Z_m = M_(m-1) ... M_1 M_0.
Earlier right-growing generic auxiliary cocycles used
  C_0 ... C_(m-1);
this TURN added `leftOrderedSourceRGChain` to use the correct
physical chronological matrix multiplication.
At each step `C_j^T B_j=I`, exact bilinear pairing preserves
  (Z_m v)^T (B_(m-1)...B_0 J)=v^T J
at arbitrary finite depth without assuming any large cumulative norm.
A finite polynomial template budget then bounds the **paired**
genuine SU2 candidate composite-source observable.

For (possibly compensated) 21x21 RG source-step residuals
`R_j`, if `x_j>=xweak>0`, `x_j-x_(j+1)>=drift>0` for j<K, and
`sum_i norm(R_j(i,alpha)-delta_(i,alpha)) <= C*x_j^(-2)`,
then the newly accepted `YM/Wilson/DriftLeftOrderedRG21.lean`
and the re-ported and audited `YM/Wilson/InverseSquareBudget.lean`
yield the **finite weak-stop** uniform estimate
  colNorm(R_(m-1)...R_0) <= exp(C/(drift*xweak))
for all m<=K, independent of K and of the number of RG steps.
The corresponding auxiliary right-ordered variant also passes strict
Lean and the genuine candidate source can be bounded under the
displayed explicit source-step inputs.

**IMPORTANT:** the actual Yang--Mills RG source matrices have NOT been
shown to have residual `O(x_j^(-2))=O(g_j^4)` after the classical /
marginal RG normalization. The drift lower bound and the precise
source-to-RG/counterterm dictionary must be checked against actual
B08/B09 dynamics. We have proved the conditional source algebra,
not the missing model inequality.

## Exact manuscript target accounting (unchanged)

- Historical original manuscript official-pin union: **34/39 = 87.18%**.
- Original IDs still unverified: **1, 24, 30, 34, 42**.
- Original30's OS E0' all-orders Schwartz distribution growth remains
  unproved from actual source norm / polymer estimates. The presently
  certified bounded composite candidate roots are only an ingredient.
- The actual source `a`-normalization, fixed-template 21-root jet,
  physical RG step residual, endpoint frame, joint 4r-coordinate Fourier
  periodization, uniform polymer derivatives/cumulants, regulator/volume
  joint limits and full tempered Schwinger hierarchy are still required.
- Original34 OS reconstruction has unproved E0' model inputs.
- Original42 complete U-I-C model assembly remains unproved.
- I7 interacting-measure global quadratic Gram frame remains **open**;
  no unconditional 4D SU2 Yang--Mills mass gap is claimed.
- The count 28+3 refers to auxiliary theorem declarations, not
  31 new original manuscript environments.

## Shortest next model-bearing node

Construct and compare the **actual** `M_{j,D}` in original manuscript
(297)--(305) and the candidate fixed-21 normalized sources. First prove
the quantitative corrected-frame entrywise/column residual
  sum_i |R_j(i,alpha)-delta_(i,alpha)| <= C*g_j^4
(or a mathematically sufficient alternative) uniformly over the actual
cutoff/volume/background families and with correct canonical source
dimension. Only then can the above new U3 drift certificate be used to
deduce a physical uniform source chart, subsequently entering the full
Original30 E0' Schwartz/Fourier chain.
