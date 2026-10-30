# Original24 LEAP: original-v133 native shell counting and exact double-root FP interface
2026-10-30; strict conditional original-environment union = 37/39 (94.87%).

## Important verified new lemma

Native shell statement is already explicit in the ORIGINAL v133 U1 TeX:
  for each physical block Delta and length shell m,
  #(X containing Delta: m<=d_j(X)<m+1)
      <= C_pol*exp(c_pol*m).
The new Lean theorem uses NATIVE integer block length (therefore shell
d=m) to prove WITHOUT an assumed total hcount:
  Σ_{X contains Delta} exp(-(kappa_R-kappa)*d(X))
    <= C_pol/(1-exp(-(kappa_R-kappa-c_pol))).
The precise necessary gap is kappa_R>kappa+c_pol.

Certified CI:
- https://github.com/penghongzhong/YM-closed/actions/runs/41044185146
  SUCCESS Lean + full type and axioms; 9003/9003.
  Module YMOriginal/Original24_NativeShellU1.lean
  theorem actual_native_U1_shell_count_to_block_norm.
No sorryAx, admit, custom axiom; standard [propext, Classical.choice,
Quot.sound] only.

The follow-up source
  YMOriginal/Original24_BalabanNativeShellRealSeries.lean
uses this lemma to DELETE the prior independent unmarked total hcount
hypothesis of the already compiled both-sectors terminal theorem,
substituting an explicit original-manuscript uniform shell counting
condition, and preserving the actual n+2 Wilson-Mayer O(aAct) conclusion.
The previous #41044548642 compiled the new terminal (9016/9016)
but failed due solely to a CI audit-file import-order error.
This was repaired and the complete official STRICT acceptance is:
- https://github.com/penghongzhong/YM-closed/actions/runs/41045067581
  SUCCESS: both complete module builds, 9003/9003 shell module,
  9016/9016 actual Bałaban native-shell terminal, all full theorem
  types and #print axioms, only core standard axioms.
  The hcount TOTAL bound is proved from the original native
  shell-count hypothesis, not an additional unproved scalar premise.

## Correct unique-q FP contacts and factorial

The separate strictly compiled branch
  ym-original24-unique-q-fp-dictionary-20261030
contains
  YMOriginal/Original24_ExactAugmentedQContact.lean
  YMOriginal/Original24_UniqueQFactorial.lean.
SUCCESS:
https://github.com/penghongzhong/YM-closed/actions/runs/41043628620
https://github.com/penghongzhong/YM-closed/actions/runs/41044678345

For the actual periodic physical q-as-a-unique-polymer species,
bulk-bulk and q-bulk chi contact exactly match the original
extended n+2 two-root Mayer graph. The augmented KP model can have
an EXTRA direct p-q contact; in the exact Mayer graph this edge is
EXCLUDED and may only be kept as a positive OVERCOUNT, not equality.
The labeled unique-q permutations give precisely
  (n+1)/(n+1)! = 1/n!
under simultaneous label-permutation invariance.

## Remaining load-bearing original #24 mathematical tasks

No, the original manuscript environment #24, B11/v124R full fixed-D
C-LOCAL-POLY-LF_D source-class closure is NOT yet fully proved by
these new lemmas. In particular:

(1) The correct finite-height two-root FP PLANAR TREE ENUMERATION
    correspondence of EXACT actual extended n+2-vertex hard-core
    Mayer spanning trees (with physical q branching and correct
    1/n!) to the augmented p-rooted KP forest is STILL UNPROVED.
    Previous final
    actual_original24_two_root_mayer_full_sum_from_U1_FP
    uses a precise BUT EXPLICIT hypothesis
    PhysicalExactTwoRootFPCriterion.
    Native shell count, q adjacency and q factorial alone
    do not logically establish it.

(2) The original published Balaban CMP119/CMP122 large-field
    RG R-history species must be proved to match the chosen
    physical periodic hard-core support/length indexing, including
    the source insertion, uniform shell count at all cutoffs,
    volumes, weak-stop levels and admissible backgrounds.
    U1Data alone is abstract and does not make this identification.

(3) Fixed-D local composite-source jets, Ward--Taylor subtraction,
    exact a^(4-d) canonical factors, B09/Original19
    counterterm mixing and source projection need to be
    TYPE-ALIGNED with the true native B11 marked post-R
    activity, not merely shown for an arbitrary scalar source.
    The older B10 Taylor lemmas and Original19 cocycle are
    reusable but their actual source dictionary is missing.

(4) The terminal theorem also needs positivity of native
    aAct_old/new and a stricter quantitative weak margin.
    These need to be derived on the original weak-coupling window
    or handled in their zero-activity case.

Historical conditional paper environments = **37/39**, original
#24 and #30 still open. I7 remains unproved as an explicit
global theorem parameter. No unconditional 4D SU2 YM mass gap.

Recommended shortest proof chain:
  Published uniform U1 RG activities
   + native uniform shell counting (now strictly Lean checked)
   + physical q contact/factorial (now strictly Lean checked)
   + EXACT finite-height FP two-root tree/forest comparison (OPEN)
  -> full n+2 connected Mayer source norm (already Lean checked)
  -> true 4D Schwartz B10 (already Lean checked)
  -> fixed-D RG counterterm/jet dictionary (OPEN)
  -> B11 original #24 strict theorem environment PASS (not yet).
