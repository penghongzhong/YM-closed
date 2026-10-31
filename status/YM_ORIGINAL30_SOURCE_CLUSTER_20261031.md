# Original 30: a common cluster hierarchy of the actual Wilson sources

Base remote commit: e7b57dd9b71f24764eb652cfd7695dc31ae6a4e8.

The previous source bound now yields a limit hierarchy without assuming
convergence on any test class. Three new modules each contain one theorem.

1. `joint_ultrafilter_compactness`: given a nontrivial regulator filter and
   a joint hierarchy with one uniform continuous-seminorm bound at each
   order, choose ONE ultrafilter refining that filter. Every order and
   EVERY full joint Schwartz test converges along this same ultrafilter.
   Bounded complex values lie in compact closed balls; their ultrafilter
   limits supply the testwise values. Linearity and continuity are derived
   from the limits and the uniform bound. The resulting hierarchy is unique
   for that chosen ultrafilter.

2. `actual_source_cluster_hierarchy`: apply this compactness result to the
   exact source-derivative joint distributions. Configuration spaces,
   probability laws, lattice sizes, Wilson words and coefficients may all
   depend on the regulator. Besides continuous link coordinates and
   0<a<=1, the material input is a SINGLE coefficient budget K across the
   family. The zero-order identity is derived from the actual finite source
   dictionary and the empty-product moment, then passed to the limit:

       H.S 0 F = F(0),
       ||H.S r F|| <= 2 exp(24576 K) r! Q_(8r,8r)(F).

3. `actual_source_diagonal_limit`: take the explicit sequence
   a_n=1/(n+1), N_n=(n+1)^2. The proof derives a_n -> 0 and
   a_n*N_n=n+1 -> infinity, and obtains the normalized hierarchy above
   along one ultrafilter refining atTop. Both regulator limits and all
   joint moments use the SAME ultrafilter. No regulator-limit or
   moment-convergence assumption is passed to this theorem.

The first theorem has the quantifier order

    exists u refining l, exists unique H, forall r F, convergence along u.

It does not choose a different extraction for each test or each order.
No countable dense test set, tensor factorization or compact-support
extension premise is needed. The source family and lattice positions are
the previously defined actual finite Wilson family, with its existing
nonnegative-site lattice geometry; the construction does not produce
translation covariance merely by taking larger boxes.

This is a CLUSTER result for the bounded-coefficient family. It does not
establish convergence along the original filter, equality of limits from
different ultrafilters, nontriviality, or the physical renormalized-source
dictionary. In particular, the required common K for the physical
renormalized coefficients is still unproved. Neither nonlinear source
counterterms nor their uniform analytic estimates are supplied here.
The spatial weight remains 8r; this is not the fixed-q OS_E0prime interface.

Verification uses Lean 4.35.0-rc3 and Mathlib
516d31250e96c4e8e76888c3d8e2e43a9642b9ee. The reproducible command is
`python3 tools/verify_original30_source_cluster.py` in the configured Lean
environment. Its strict builds, untruncated full types, printed source and
regulator definitions, axiom lists, three kernel-replay logs, and recursive
project dependency hashes are in
`verification/original30-source-cluster-20261031/`.
The recorded status is `PASS_ACTUAL_SOURCE_COMMON_CLUSTER_LIMIT`. All three
new theorem roots use only propext, Classical.choice and Quot.sound; the
source scan covers 28 project modules with no proof placeholders or new
axiom declarations. The full type/definition output has 899221 characters
before compression, with no printer elision.

No new original manuscript environment is accepted on these supporting
results. Original 30 and Original 24 remain OPEN. The original conditional
ledger remains **37/39**; **I7 remains an explicit unproved premise**.
