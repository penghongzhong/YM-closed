# Original 30: bare joint linear-weight bridge

Base: efa6f887167ac59a4d23a6e3997f556ad5f50c84. Lean 4.35.0-rc3;
Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

`YMUIC.Original30.bare_joint_linear_weight_factorial_bound` applies to the
actual finite-lattice bare Wilson joint probability moment. For a uniform
polynomial coefficient budget K and the stated measurability hypothesis, it
proves integrability and

    |S_{r,a,N}(f)| <= 2 exp(24576 K) r! Q_{8r,8r}(f),

where Q is `jointSchwartzControl`, uniformly for 0<a<=1 and all N. This is
derived from the existing all-volume bare bound and the exponential series.
Targeted compilation, complete type/axiom audit, and leanchecker replay passed;
the evidence is in `verification/original30-bare-linear-growth-20261031/`.
Only propext, Classical.choice and Quot.sound occur.

Osterwalder--Schrader (1975), p. 287, distinguishes E0' in (4.1), with
the joint norm index sn, from E0'' in (4.2), with a different norm. The linear
index suggests a shorter E0' route than the existing fixed-spatial-weight
interface, but the equivalence and constants between the published norm and
the Lean Q above remain to be proved. No E0'' assertion is made.

This is a bare-source result, not the renormalized physical source or a
same-net continuum result. It does not accept Original 30; the historical
standard-input-assisted conditional ledger remains 37/39, with Original 24
and 30 open and I7 an explicit unproved premise.
