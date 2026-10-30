# Original24 next shortest proof route: genuine rooted KP, not full FP tree enumeration

2026-10-30. STRICT tally 37/39; original 24 and 30 open. I7 remains unproved.

This is a RESEARCH PLAN, NOT a Lean proof of the original B11 theorem.
It is intentionally placed in the same fixed-D terminal branch, rather
than spawning another speculative list of helper theorem environments.

## New efficient route from a PUBLISHED theorem

The Kotecký--Preiss abstract hard-core polymer cluster theorem
(CMP 103 (1986), 491--498) and modern printed versions state that
if every polymer gamma obeys
   sum_{eta incompatible gamma}
      |z_eta| exp(a(eta)+b(eta)) <= a(gamma)
then the cluster expansion converges absolutely and provides a
uniform *pinned cluster* bound; see, for example, the explicit
Theorem 4.2 and formula (20) in
https://link.springer.com/article/10.1007/s00220-026-05623-3
and original 1986 article
https://www.math.ucla.edu/~biskup/290k.1.24w/PDFs/Kotecky-Preiss.pdf .

Crucial caution: the usual printed bound on clusters that touch
a test polymer p only counts clusters connected *without p*.
The C29 Mayer coefficient uses a connected graph INCLUDING p:
distinct bulk components may be joined through p.
Thus simply substituting this "cluster incompatible with p"
inequality for PhysicalExactTwoRootFPCriterion is NOT valid.

The correct finite-model route is instead:

1. Adjoin TWO named source species p,q to the actual bulk Γ.
   p carries an independent zero/test activity, q carries
   positive epsilon, and bulk carries lambda*|z|.
   Use a symmetric REFLEXIVE incompatibility:
   bulk-bulk exact original chi contact;
   p-bulk and q-bulk exact original Wilson support contact;
   p-q COMPATIBLE by definition (NO root-root bond).
   The published hard-core polymer theorem works for arbitrary
   symmetric incompatibility, so p-q need not obey naive overlap.
   In particular, no false p-q source bond is introduced.

2. Prove the genuine p-rooted CLUSTER DERIVATIVE / pointed
   Ursell bound (equivalent to standard Kotecky--Preiss
   pinned cluster theorem, but NOT merely the theorem for
   clusters touching p), or use the published root
   Kirkwood--Salsburg ratio bound with exactly this scope.

3. The connected Ursell sum with p once and q exactly once
   equals the ORIGINAL n+2-vertex graph sum. The q label
   occurs in n+1 positions, so
      (n+1)/(n+1)! = 1/n!.
   This factorial identity and physical bulk-q adjacency
   are ALREADY independently kernel-verified:
   https://github.com/penghongzhong/YM-closed/actions/runs/41044678345

4. The published KP hypotheses for augmented Γ+{p,q} are
   derived from the original U1 per-block bound and the
   strict weak margin. Earlier genuinely compiled modules:
     Original24_AugmentedSecondRootKP.lean
     Original24_ExplicitTwoFugacityKP.lean
   The explicit fugacities
     lambda=delta/(4 B A),
     epsilon=delta/(8 B exp(kappa*card(rootQ)))
   satisfy B(lambda*A+epsilon*E) = 3delta/8, provided
     delta>0, A>0, 4B A<=delta.
   The resulting extraction of exactly one q and at least
   one bulk history uses 1/(lambda*epsilon)=O(A),
   already verified in
   https://github.com/penghongzhong/YM-closed/actions/runs/41034179841 .

5. Use the REAL source norm and fixed-D counterterm
   cocycle from the current single terminal:
     Original24_FixedDMainCore.lean .
   This is a quantitative source-lift / local projection
   algebraic theorem only; the physical R-history source
   dictionary and fifth-order RG Taylor remainder still
   have to be proved, not postulated.

## Important status

The published K-P universal analytic theorem is a legitimate
external literature input if its hypotheses and pointed-root
conclusion EXACTLY match the model. Its invocation in Lean
can be an explicit proof parameter (like published U1),
but no external theorem input may silently contain the
FULL original desired B11 source-class conclusion.
The actual model is not closed until its true CMP119/122
history graph, uniform physical norm and fixed-D RG jets
are derived.

Do not increment 37/39 merely because the candidate
fixed-D terminal module compiles.


## Latest one-environment strict Lean receipt (official)

Actions #41084019357:
https://github.com/penghongzhong/YM-closed/actions/runs/41084019357

SUCCESS, 9017/9017 fixed-pin Lean tasks; warnings-as-errors complete;
full theorem type printing, axiom audit, no sorryAx or custom
axiom. Source: YMOriginal/Original24_FixedDMainCore.lean.

Theorem: YMUIC.Original24.original24_fixedD_same_source_full_series_and_cocycle.

This is ONE substantial FIXED-D conditional terminal environment
rather than a series of unconnected auxiliary lemma files:
actual native-shell Balaban old/new source activities and exact
n+2 hard-core two-root complex Mayer series; absolute full-series
summability and quantitative norm of the SAME lifted source;
same finite-dimensional continuous-linear source map and
Original19 ordered invertible counterterm cocycle; true jet
projection, local/remainder splitting, and exact transported
dual source pairing.

IMPORTANT: this new proved conditional terminal is not the
UNCHANGED original manuscript thm:B11-repair environment. It
still has explicit PhysicalExactTwoRootFPCriterion inputs,
abstract U1Data not identified with the actual CMP119/122
Yang--Mills history construction, and a supplied real-linear
sourceLift not derived from the true composite-source chart.
It does not yet supply the physical RG fifth-order B10
localization/canonical a^(4-d) source coordinates.
Original-environment conditional historical count remains
37/39, not 38/39.
