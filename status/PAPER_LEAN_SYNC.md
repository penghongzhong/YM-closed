# Paper ↔ Lean synchronization ledger

| Order | Paper node | Lean file | Class | Status |
|---:|---|---|---|---|
| 0 | §1 basic objects / positivity | `Lean/Section01/T000_Foundations.lean` | internal elementary | PASS |
| 1 | §2 `thm:U1` | `Lean/Section02/T001_U1_PublishedInterface.lean` | published external interface | EXTERNAL-INTERFACE PASS |
| 1A | §2 small-field `δ_sf` / geometric-series core | `Lean/Section02/T001A_SmallFieldGeometric.lean` | internal analysis | PASS |
| 1B | U2 `Wbound`: `0 ≤ W_p ≤ 4` | `Lean/Section03/T002_WilsonRootBound.lean` | internal SU(2)/matrix bound | PASS |
| 1C | U2 `Dp/Kr`: exact source multiplier bound | `Lean/Section03/T003_SourceMultiplier.lean` | internal complex analysis | PASS |
| 1D | U2 B01G finite block/polymer/rooted-cluster semantics | `Lean/Section03/T004_B01G_FiniteClusterObjects.lean` | internal finite combinatorics | PASS (12/12) |
| 2A | `lem:root-distance` local polymer metric step | `Lean/Section03/T005A_RootDistance_LocalPolymerGeometry.lean` | internal graph geometry | PASS |
| 2B | `lem:root-distance` finite mapped-walk triangle budget | `Lean/Section03/T005B_RootDistance_MappedWalkBudget.lean` | internal graph metric | PASS |
| 2C | `lem:root-distance` support-anchor one-edge budget | `Lean/Section03/T005C_RootDistance_SupportAnchorEdgeBudget.lean` | internal graph geometry | PASS |
| 2D | `lem:root-distance` linear path-weight arithmetic | `Lean/Section03/T005D_RootDistance_PathWeightArithmetic.lean` | internal arithmetic | PASS |
| 2E | `lem:root-distance` simple-path bookkeeping | `Lean/Section03/T005E_RootDistance_SimplePathBookkeeping.lean` | internal finite graph arithmetic | PASS |
| 2F | `lem:root-distance` getVert/support sum bridge | `Lean/Section03/T005F_RootDistance_GetVertSupportSum.lean` | internal finite-sum bookkeeping | PASS |
| 2G | full `lem:root-distance` assembly | `Lean/Section03/T005G_RootDistance_FullAssembly.lean` | internal graph geometry | PASS |
| 3 | `lem:root-tree-majorant` | next canonical files | internal tree/KP combinatorics | QUEUED |

## Paper synchronization completed at root-distance

CURRENT TeX now explicitly defines:

[
operatorname{dist}_j(A,B)
=min_{ain A,bin B}operatorname{dist}_j(a,b),
qquad
R_{m rt}
=sup_{j,Lambda,r}operatorname{diam}_j(B_j(r)),
]

and records the Lean-certified choices

[
c_{m geo}=chi+2,
qquad
c_{m rt}=chi+4R_{m rt}.
]

The PDF generated from this CURRENT TeX passes XeLaTeX CI.

## Synchronization invariant

`Lean failure → exact TeX formula/theorem → classify implementation/API vs mathematics → repair CURRENT only if mathematical → rerun Lean → update ledgers.`

| 3A | `lem:root-tree-majorant` KP scalar core | `Lean/Section03/T006A_RootTreeMajorant_KPScalarCore.lean` | internal scalar/exponential algebra | PASS |
| 3B | `lem:root-tree-majorant` finite contact counting | `Lean/Section03/T006B_RootTreeMajorant_ContactCounting.lean` | internal finite double counting | PASS |
| 3C | `lem:root-tree-majorant` finite-height recursion | `Lean/Section03/T006C_RootTreeMajorant_FiniteHeightRecursion.lean` | internal finite recursion | PASS |
| 3D | `lem:root-tree-majorant` full child-sum | `Lean/Section03/T006D_RootTreeMajorant_FullChildSum.lean` | internal contact/KP assembly | PASS |
| 3E | `lem:root-tree-majorant` first-root sum | `Lean/Section03/T006E_RootTreeMajorant_FirstRootSum.lean` | internal root counting | PASS |
| 3F | `lem:root-tree-majorant` FP rooted-tree enumeration interface | `Lean/Section03/T006F_RootTreeMajorant_FernandezProcacciInterface.lean` | published external combinatorial interface | EXTERNAL-INTERFACE PASS |
| 3G | full `lem:root-tree-majorant` assembly | `Lean/Section03/T006G_RootTreeMajorant_FullAssembly.lean` | internal assembly over external tree-enumeration interface | PASS |
| 4A | `lem:root` distance/exponent extraction | `Lean/Section03/T007A_RootEntropy_DistanceExtraction.lean` | internal scalar geometry | PASS |
| 4B | `lem:root` Penrose + bounded roots | `Lean/Section03/T007B_RootEntropy_PenroseRootFactor.lean` | external Penrose pointwise interface + internal root factor | PASS |
| 4C | `lem:root` nonnegative infinite-sum comparison | `Lean/Section03/T007C_RootEntropy_TsumComparison.lean` | internal analysis | PASS |
| 4D | full `lem:root` assembly | `Lean/Section03/T007D_RootEntropy_FullAssembly.lean` | internal assembly | PASS |

| 5A | `lem:U2-source-analyticity` finite-cluster entire/zero-source | `Lean/Section03/T008A_SourceAnalyticity_FiniteClusterEntire.lean` | internal complex analysis | PASS |
| 5B | explicit cluster Fréchet derivative | `Lean/Section03/T008B_SourceAnalyticity_FrechetDerivative.lean` | internal complex Fréchet calculus | PASS |
| 5C | joint `ℂ²` `tsum` differentiability | `Lean/Section03/T008C_SourceAnalyticity_TsumEngine.lean` | internal Banach analysis | PASS |
| 5D | polydisc geometry + uniform M-test | `Lean/Section03/T008D_SourceAnalyticity_PolydiscAssembly.lean` | internal topology/analysis | PASS |
| 5E | derivative tree majorant | `Lean/Section03/T008E_SourceAnalyticity_DerivativeMajorant.lean` | internal norm estimate | PASS |
| 5F | full `lem:U2-source-analyticity` assembly | `Lean/Section03/T008F_SourceAnalyticity_FullAssembly.lean` | internal assembly | PASS |

## Paper synchronization completed at source analyticity

CURRENT TeX now uses joint complex Fréchet differentiability on `ℂ²` as the
formal meaning of joint holomorphy. It explicitly defines `π₁, π₂`,
the cluster derivative `𝒟_Γ`, the derivative constant
`K'_{r'} = 8 exp(4r') (exp(4r') + 1)`, and the rooted-tree majorant
used for derivative summability. The one-variable `analyticOnNhd` API is
not used as a surrogate for joint holomorphy.

Full synchronized verification run #58: Lean logical order SUCCESS and
CURRENT/v128 PDF compilation SUCCESS. Static TeX audit:
duplicate labels 0; missing refs 0; forward refs 0.
