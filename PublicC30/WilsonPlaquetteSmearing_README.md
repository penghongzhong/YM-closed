# New actual Wilson-root source to Schwartz test bridge

## Exact source, no formalized assumptions on source map

For any finite set of plaquettes `S`, any genuine holonomy-valued family
`U : P → SU(2)`, any sample positions in Euclidean `R⁴`, any spacing
`a ≥ 0` and any complex Schwartz function `f`, construct the **actual
point-evaluation Wilson plaquette source**

`J[a,S,U](f) = Σ(p∈S) a⁴·(2 − Re Tr U(p))·f(x(p))`.

The SU(2) root bounds `0 ≤ W(p) ≤ 4` are kernel-proved by the exact
source from `Lean/Section03/T002_WilsonRootBound.lean`, copied without
modification to `YM/Wilson/RootBound.lean`.

The **new** norm estimate is

`|J[a,S,U](f)| ≤ 4a⁴ #S · p₀,₀(f)`.

If the lattice sampling geometry supplies the **explicit** counting bound
`a⁴ #S ≤ V` (which remains a hypothesis), then

`|J[a,S,U](f)| ≤ 4V · p₀,₀(f)`.

No Wilson-source seminorm assumption is used. All gauge holonomies and
plaquettes are quantified, and the constant is independent of U and a
once the physical volume/count bound holds.

**Scope:** This is one concrete single-plaquette Wilson-root Schwartz
smearing map. It does not yet establish the full renormalized connected
Wilson/cluster generating functional, higher source derivatives,
`C²` source-chart matching, dyadic tensor budget, exact
`E0′` bound, or manuscript Original30. Never promote 34/39 solely
from this bridge. Standard tools: Lean 4.35.0-rc3, Mathlib 516d3125.

## Eliminating the packing hypothesis on an actual hypercubic regulator

For a four-dimensional periodic lattice `(Fin 4 → Fin N)` with six
unoriented plaquette orientations per vertex, the exact number of
plaquettes is `6 N⁴`. For *any* subset `S` and spacing `a ≥ 0`, if
the physical side `a N ≤ L`, then the new Lean theorem derives
`a⁴ #S ≤ 6L⁴`; the geometry bound is no longer a free input.
Therefore, for all SU(2) holonomy families and all complex Schwartz tests,

`|J[a,S,U](f)| ≤ 24 L⁴ p₀,₀(f)`.

The only scale parameter in this bound is the physical box length L.
No bounds on the gauge configurations, no Wilson-source seminorm input and
no arbitrary plaquette packing constant are assumed. The theorem is still
for the raw plaquette source, not the RG-connected Wilson hierarchy.

## Actual continuous complex-linear operator

Next source `PublicC30/WilsonSchwartzCLM.lean` constructs from genuine
Mathlib Dirac point evaluations a Schwartz-space continuous complex-linear
map, proves equality with the Wilson plaquette scalar smearing, and derives
finite physical-box control. Both complex linearity and continuity follow
from the constructed CLM and are not supplied as source hypotheses.

This remains a raw plaquette source, not the full RG source of Original30.

## Explicit fixed-support local chart (pending exact-pin CI)

The genuine SU(2) Wilson Schwartz CLM is localized to a finite set of
plaquettes in the global `N^4` periodic regulator. Assume only an explicit
**injective chart encoding** of the marked local plaquettes in a local
`M^4` box, with fixed physical side `a M ≤ R`. The new theorem derives

`|J_(a,S,U)(f)| ≤ 24R⁴ · p₀,₀(f)`,

independently of the regulator's total physical length and site count N.
This removes the `L^4` **volume growth** for a test family with a common
local chart. The existence of a common chart for the actual Wilson source
support is an explicit, unproved geometric dictionary; it is not inferred
from the source field nor treated as a free source bound. The full RG
connected source hierarchy and all-orders OS E0′ remain unproved.
