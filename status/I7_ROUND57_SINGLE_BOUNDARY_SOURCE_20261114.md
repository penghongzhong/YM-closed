# Round 57 — actual Wilson single-boundary-source reduction
Date: 2026-11-14. Branch: ym-i7-boundary-response-20261114.
REAL PHYSICAL I7: OPEN. Historical 39/39: CONDITIONAL.

## A. Strict Lean achievement

YMOriginal/OriginalI7_BoundaryResponse.lean:
  YMUIC.I7Boundary.cube_half_from_contact_response.
CI: https://github.com/penghongzhong/YM-closed/actions/runs/43545555640
SUCCESS with Lean 4.35.0-rc3 / Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee,
only [propext, Classical.choice, Quot.sound]; no sorry, admit, added axiom.

For an actual forest-gauge cube of side n=2m, Proposition 260 of the 2026
Bhattacharjee et al preprint supplies (as an EXTERNAL claim):
  sum_(j in c outside V) b(V,j) <= 10 m^3-2 m^2,
  N_n = m^4,
where b(V,j) counts interior links sharing plaquettes with exterior j.

The SOLE NEW model-facing sufficient condition is
  (B57) C_(V,j) <= (m/20) b(V,j)   for all exterior j, all backgrounds
and regulators/volumes, where C is the REAL full Wilson conditional-law W1
influence. Then the Lean scalar inference proves
  K_c <= (m/20)(10m^3-2m^2) <= m^4/2 = N_n/2.
By the conditional 2026 preprint Theorem 43, D(2m,1/2) produces
  q* = 1/sqrt(2), eta* = 1-1/sqrt(2),
  gap(H) >= log(2)/(4 a*) >= [log(2)/(4 c+)]Lambda_YM,
with B08 physical clock a*=n_* a0, n_cube=2 n_*.
No actual Wilson proof of (B57) has been obtained.

## B. Exact model source identity, proven on paper

Fix the physical finite Wilson measure after a fixed forest gauge, and
an active-link cube V. For exterior configuration eta, write the conditional
Gibbs specification with exact Wilson action A:
 gamma_eta(dU_V) = exp(A(U_V,eta)) / Z(eta) * dHaar^(V)(U_V).

Let eta' differ from eta only at one exterior active link j, and define
 Delta_j(U_V) = A(U_V,eta')-A(U_V,eta).
All terms constant in U_V cancel on normalization. The only variable-
dependent terms of Delta_j lie on plaquettes that contain j and an
active link inside V. In 4D, a lattice link lies on at most six
unoriented plaquettes, so the boundary source is genuinely local.

For any bounded real interior observable F, direct Gibbs-density algebra
gives EXACTLY:
 gamma_eta'(F) = gamma_eta(F exp(Delta_j))/gamma_eta(exp(Delta_j)).
Thus
  (57.3) gamma_eta'(F)-gamma_eta(F)
       = Cov_gamma_eta(F, exp(Delta_j)-1)
           /gamma_eta(exp(Delta_j)).
The denominator is strictly positive. No mass-gap claim appears in this
identity.

By compact-metric Kantorovich--Rubinstein duality for sum-distance d_V,
with the supremum over real 1-Lipschitz functions F:
  (57.4) C_(V,j)
    = sup_(eta,eta':differ only j) sup_(Lip F <= 1)
       |Cov_gamma_eta(F,exp(Delta_j)-1)|
          /(delta(eta_j,eta'_j)*gamma_eta(exp(Delta_j))),
with distinct j-th exterior variables.

Hence the exact physical RED57 is:
  for all actual exterior pairs differing only at j and ALL
  real Lip_(d_V) F<=1,
  |Cov_gamma_eta(F,exp(Delta_j)-1)|
   <= (m/20)*b(V,j)*delta(eta_j,eta'_j)
       *gamma_eta(exp(Delta_j)).
This is equivalent to B57 after KR duality; it is NOT a proof of B57.
Its gain is to identify the EXACT local crossing-plaquette Wilson root
to which a uniform connected-source bound must be applied.

## C. Why existing Original24 is insufficient

Original24_BalabanTwoRootRealFullSeries.lean bounds old/new-R Mayer sources
with a fixed Wilson-polynomial coefficient budget and separate printed
geometry and graph hypotheses. It is not an exact equality with the
COMPLETE Wilson conditional measure, including the IR effective action.
RED57 requires ALL 1-Lipschitz F of the cube; density of Wilson words alone
does not control their approximation coefficient budgets. It also needs a
relative denominator and a division by the change in boundary-link metric.
The supremacy is over ALL exteriors, not average over typical histories.

Precisely: if X is Bernoulli(epsilon) and Y follows X with probability
1-rho (otherwise flips), 0<rho<1/2, the strictly positive conditional
laws have boundary W1 sensitivity 1-2rho, whereas
  |Cov(X,Y)| = (1-2rho)*epsilon*(1-epsilon) -> 0
as epsilon->0. Therefore averaged/rare-background covariance bounds by
themselves cannot control worst-boundary W1 coefficients. This is a
logical counterexample, not a Yang--Mills counterexample.

## D. Final exact RED (unproved)

Use existing Wilson gauge/word dictionaries to identify each crossing
plaquette's local change-of-boundary insertion exp(Delta_j)-1, in the SAME
full Wilson Gibbs conditional law. Prove RED57 uniformly over the cutoff,
volumes, all exteriors and every 1-Lipschitz real interior observable.
No mere local word bound or rare-field smallness can replace this norm.

The external Bhattacharjee et al. result is a 2026 preprint rather
than a peer-reviewed theorem; its model-level and limit transfer
cannot be silently promoted to accepted published input.

Accepted: 1 new conditional-to-cube Lean arithmetic theorem.
Paper: exact Wilson Gibbs boundary tilt identity.
UNPROVED: physical RED57, physical I7, unconditional Clay result.
