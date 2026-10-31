# Bare Wilson joint moments: radial zero-order OS bridge

Base: efa6f88, with the 35160399/6681519 code tree; Lean 4.35.0-rc3,
Mathlib 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.

Define `osRadialZeroNorm r f` to be the actual supremum of
`(1+‖x‖²)^(4r) ‖f x‖` over joint 4r-dimensional space. Finiteness is proved
from the Schwartz property; it is not an extra assumption. This is the zero
derivative term of the radial norm (2.1) of Osterwalder--Schrader 1975 at
index 8r; it is not the full norm nor the distinct E0'' norm.

For the existing actual bare Wilson joint probability moment, the theorem
`bare_joint_os_radial_zero_bound` proves its integrability and
`|S_(r,a,N)(f)| ≤ 2 exp(24576K) r! osRadialZeroNorm r f`, for every r,
every 0<a≤1 and every N, assuming the existing nonnegative, uniform Wilson
polynomial coefficient budget K and explicit strong measurability. No higher
derivative norm comparison, r-dependent spatial weight loss, or new hypothesis
asserting the desired estimate occurs.

The complete norm dictionary (including the paper's subspace restriction),
the renormalized physical source, the regulator-uniform model bound, and a
same-net continuum Schwinger hierarchy remain open. This is not acceptance of
Original30 or a physical OS reconstruction. I7 remains an explicit unproved
premise; the conditional original ledger remains 37/39.

Validation: targeted `lake build YMOriginal.Original30_OSZeroOrderBridge`,
`lake env lean -DwarningAsError=true .../ExactTypes.lean`, and
`lake env leanchecker -v YMOriginal.Original30_OSZeroOrderBridge` each exited
0. Each command used Lean 4.35.0-rc3 and LD_PRELOAD=/tmp/ym-lean/proc-self.so
to correct the runtime's process-executable lookup. Output logs accompany this
file. Complete type output has no truncation markers or `sorryAx`. Axioms of
the six checked theorems are only propext, Classical.choice, Quot.sound.
Source SHA256: 63dd39752eb58d3ad71828d32d35d153eb5588d5a1630efa29180c0b5e1c98ef.
