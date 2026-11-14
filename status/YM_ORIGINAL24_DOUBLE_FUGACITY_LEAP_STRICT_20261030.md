# Original24 — strict two-fugacity KP / rooted double-source gain (2026-10-30)

## Official Lean receipt

Repository: penghongzhong/YM-closed
Branch: ym-original24-double-fugacity-20261030
Toolchain: leanprover/lean4:v4.35.0-rc3
Mathlib: 516d31250e96c4e8e76888c3d8e2e43a9642b9ee

Strict accepted CI:
https://github.com/penghongzhong/YM-closed/actions/runs/41034179841
SUCCESS: full module builds, -DwarningAsError=true, all full theorem
types, and #print axioms. The source module-build final count
was [8983/8983].
Only [propext, Classical.choice, Quot.sound] in new theorem dependencies.
No custom axioms, sorry, admit, or sorryAx.

Sources:
- YMOriginal/Original24_DoubleFugacitySelection.lean
- YMOriginal/Original24_ExplicitTwoFugacityKP.lean
- YMOriginal/Original24_DoubleFugacityFPTerminal.lean
Workflow: .github/workflows/ym-original24-double-fugacity.yml

## New mathematical statement

The complete two-Wilson-root n+2-vertex Ursell graph cannot
legitimately delete the second root q: q may have multiple
bulk children. An augmented physical U1/KP model introduces
one named second-root species q with positive fugacity epsilon.
The positive rooted forest also allows repeated q copies,
while a nonnegative double-fugacity extraction selects EXACTLY
one q and at least one genuine physical bulk polymer.

Let
 B = (2chi+1)^4,
 delta = kappa - cGeo*mu > 0,
 E = exp(kappa*card(rootQ)) > 0,
 A = aAct > 0.
Assume actual per-block UNMARKED physical U1 activity norm:
    sum_{X covers Delta} ||z(X)|| exp(kappa*d(X)) <= A,
and actual periodic finite support size <= native length.
The available weak-margin requirement is
    4*B*A <= delta.
One can CONSTRUCT, not assume, the fugacities
    lambda  = delta/(4*B*A),
    epsilon = delta/(8*B*E),
with lambda>=1, epsilon>0 and
    B*(lambda*A+epsilon*E) = 3*delta/8 <= delta/2.
Moreover
    (lambda*epsilon)^(-1) =
       (32*B^2*E/delta^2)*A.

The unaltered U1 bulk coefficients rescaled by lambda, plus ONE
second-root species of fugacity epsilon, feed directly into the
previously checked actual 4D periodic augmented U2/KP recursion.
The FULL nonempty first-root forest at every finite height h obeys
    exp(S_h(rootP; lambda*z, epsilon*q))-1
      <= exp(card(rootP)*delta/2)-1.

For a finite nonnegative labeled tree family with bulkCount>=1
and qCount=1, elementary EXACT coefficient extraction gives
  (lambda*epsilon) sum_selected w(T)
       <= sum_all w(T) lambda^bulkCount(T) epsilon^qCount(T).

The latest Lean terminal
  original24_two_root_tree_O_aAct_from_U1_and_FP
deduces, under an explicit actual finite-height FP enumeration
interface for the same augmented tree family,
  sum_selected w(T)
   <= (32*B^2*E/delta^2)
      *(exp(card(rootP)*delta/2)-1)*A.
This restores the ORIGINAL O(A) gain, including when q is a
high-degree branch hub; no already-controlled two-root Ursell
series is among the theorem premises.

## What is NOT yet proved / counted

The manuscript original environment #24 (v124 source-class
C-LOCAL-POLY-LF_D=CLOSED for each fixed D) remains open.
The historical conditional original-environment union remains
37/39=94.87%. Original30 is also open; I7 is an UNPROVED
explicit theorem input. No unconditional SU2 YM continuum/mass-gap
claim is justified.

The exact outstanding Original24 dependencies:
1. Identify the finite-height FP enumeration hFP in the latest
   terminal theorem with the ACTUAL n+2-vertex two-root
   spanning-tree families already modeled in
   Original24_ExactExtendedTwoRootMayer and
   Original24_ExactExtendedWeighted. Check every 1/n! factor,
   repeated q species and root--root edge exclusion.
   The previous single-root model is NOT equivalent!
2. Prove the specific CMP119/CMP122 Bałaban effective old/new-R
   histories produce the above hard-core polymer activities,
   with the SAME native support, length, background, scale,
   source-insertion and regulator uniformity. The abstract
   U1Data interface and a generic finite graph do not supply
   this identification automatically.
3. Derive the required uniform unmarked history count and
   strong weak-coupling smallness, including the possible
   A=0 case.
4. Match the fixed-D normalized source jets, canonical a^(4-d),
   actual B09/Original19 source counterterm cocycle and
   the full post-R fourth-order localization under the
   unchanged source-class theorem statement.

Do not promote 37/39 to 38/39 based on the new 3 subsidiary
theorems; the genuine original-env #24 test must itself compile
with every nonpublished model input proved or clearly classified.
