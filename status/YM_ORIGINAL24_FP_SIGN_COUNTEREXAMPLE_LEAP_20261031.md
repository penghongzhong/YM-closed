# YM Original24: sign audit of unproved PhysicalExactTwoRootFPCriterion

Date: 2026-10-31. Repository: penghongzhong/YM-closed.
This is a mathematical obstruction and source audit, not an acceptance
certificate for original manuscript environment 24.

## Key finding

The current code

  YMOriginal/Original24_ExactRealTwoRootFPSeries.lean
    def PhysicalExactTwoRootFPCriterion

asks for a positive two-root n+2 Mayer tree sum, UNWEIGHTED on its LHS,
to be bounded by the q-augmented KP forest

  exp(F_h(p;lambda*z,epsilon*q; cGeo*mu))-1,

which has the vertex factor exp((cGeo*mu)*d) for every polymer.
Its type quantifies over arbitrary real cGeo and mu and does NOT
require cGeo*mu >= 0. The claim therefore CANNOT hold for every
instance when physical polymer sizes are strictly positive.

## An explicit finite 4D periodic counterexample (mathematical)

N=1, chi=0, Gamma=Unit, rootP=rootQ={the unique periodic block}.
Each bulk species has support the unique block, activity z=1,
size d=1. The special q species also has support one block and size 1.
The exact original n=1 graph is the path p -- X -- q with exactly
one spanning tree; 1/1! = 1. Thus choose lambda=epsilon=1,h=3:
the unweighted left side of the claimed criterion is exactly 1.

Set mu=1 and cGeo=log(1/16), so cGeo*mu<0 and all augmented
vertex activities equal eta=1/16. Every species has both types as
KP children. Define

  H_0=1,
  H_(k+1)=exp(2eta H_k),
  F_3=2eta H_3.

Because exp(1/4)<2, induction gives H_k<=2 for every k:
if H_k<=2, 2eta H_k<=1/4, H_(k+1)<=exp(1/4)<2.
Therefore F_3<=1/4 and

  exp(F_3)-1 <= exp(1/4)-1 <1.

In fact F_3 ~0.144363507 and exp(F_3)-1 ~0.155303993;
the strict discrepancy is proved by rational/exponential inequalities,
not numerical floating point.

The scalar inequality and finite-parameter exponent are in:
  YMOriginal/Original24_FPNegativeSignAudit.lean.
This file has been submitted for official pinned CI, but a successful
kernel audit of its scalar statements is NOT YET equivalent to a
formal Lean instantiation of every actual periodic definition.
Do not advertise a full Lean counterexample until that link is proved.

## Required correction

Use an explicit physical admissibility premise:
  0 <= cGeo * mu
(with integer d>=0 and q card>=0), or weight the exact tree
coefficients on the left with the SAME exponential physical size
weights used in the q-augmented KP right side.

The intended strong but mathematically credible finite-height
target, with fixed-q factorial absorption, is:

  (for all lambda>=1,epsilon>0,h)
  sum_(n=1)^(h-2) lambda^n*epsilon * exactTwoRootTreeMajorant(n,z)
     <= exp(F_h(p;2*lambda*z,epsilon*q))-1,

under 0<=cGeo*mu and appropriate height bookkeeping.
**This all-n enumeration remains UNPROVED in Lean, irrespective
of the now-verified graph embedding, n=1 KP coefficient, doubling
of bulk fugacity, and uniform KP recursion.**

## Manuscript count and other gaps

Historical original-environment conditional union remains 37/39.
Original 24 and 30 are unaccepted. I7 is an unproved explicit
global premise, no unconditional Yang--Mills mass-gap conclusion.

The true CMP119/CMP122 Bałaban R-history/polymer dictionary and
canonical a^(4-d) source jet identification are also still open.
The previous strict fifth-Schwartz full scale tail
Actions #41135883914 is valid only under its explicitly stated
source-weighted Penrose/FP previous-input hypotheses.

Do not count mathematical inconsistency detection or new helper
statements as increasing 37/39.

Official new source branch: ym-original24-fp-sign-audit-20261031.
