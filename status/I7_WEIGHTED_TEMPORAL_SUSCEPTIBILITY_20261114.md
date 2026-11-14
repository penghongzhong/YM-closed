# I7 physical Wilson susceptibility certificate — Round 55

Date 2026-11-14
Status: a rigorous abstract equivalence, **NOT** an SU(2) mass-gap proof.

## Positive temporal moment criterion

For each regulator k, a positive self-adjoint contraction T_k on the OS physical nonvacuum Hilbert space H_k and a dense family of centered positive-time Wilson-loop vectors v_(k,gamma), set

  a_(k,gamma)(n) := <v_(k,gamma),T_k^n v_(k,gamma)> >= 0.

Fix a physical positive time tau_k >= tau_0 > 0. The following are equivalent in the sense that the parameters may be shrunk to a positive margin:

(A) There exists a regulator-uniform q in (0,1) such that T_k <= q I for all k.

(B) There exists a COMMON R>1 such that for every k,gamma,

  S_(k,gamma)(R)
   := sum_(n>=0) R^n a_(k,gamma)(n) < infinity.

No bound on S_(k,gamma)(R) uniform in k or gamma is requested.

Proof A->B: choose 1<R<q^(-1), then
  a_n <= ||v||^2 q^n,
  S(R) <= ||v||^2/(1-Rq).

Proof B->A: for each k,gamma, nonnegative terms imply
  a_n <= S_(k,gamma)(R) R^(-n).
The positive-transfer diagonal spectral-projection lemma yields
  T_k <= R^(-1) I
for all k. This is the same uniform I7 with eta = 1 - R^(-1)>0.

Equivalently, a common radius >1 for the **physical OS-positive single-loop temporal moment generating functions** is exactly what is needed. This presentation may be closer to the weighted Fernández--Procacci / Penrose sum machinery than attempting each Gram inequality directly.

## Exact RED to link Original24 to this criterion

Establish a TRUE physical connected Wilson covariance identity, for every positive-time single loop gamma and every time translation n*tau_k, such that the combined weighted time-separated series

  sum_(n>=0) R^n |
       Cov_k(Theta W_gamma, Translate_(n tau_k) W_gamma) |

is summable, with ONE R>1 uniform across k,gamma and no time-wrap.

The old/new-R Mayer series norm and rooted distance bounds alone are not an identity with complete physical covariance. They control named remnant polymer channels; the full low-frequency infrared effective sector and source dictionary remain OPEN. A fixed-in-n error floor would destroy B.

A common R cannot be obtained merely from qualitative E4 clustering. Counterexample: T e_j=exp(-1/j)e_j on l2(N), all finite vectors mix, but no common R>1.

The weighted temporal susceptibility criterion is NOT a new outside assumption accepted as proof. It is an equivalent quantitative restatement of the actual physical IR task. No I7 or Clay closure is claimed.
