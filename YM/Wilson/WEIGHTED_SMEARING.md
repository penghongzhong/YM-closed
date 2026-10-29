# C29 Original30: actual finite-lattice Wilson smearing with Schwartz decay

This standalone public proof imports the *same* SU(2) plaquette root
`W_p=2-Re Tr(U_p)` and the *same* `SchwartzMap ℝ⁴ ℂ` as the previous
Wilson root certificate. For arbitrary finite plaquette index set `P`,
positions `x_p∈ℝ⁴` and complex quadrature weights `w_p`, the
source is **actually defined**, not supplied as an abstract functional:

`S_P(f,U)=∑_{p∈P} w_p f(x_p) W_p(U)`.

The Lean target first derives from the *actual Schwartz seminorm definitions*

`(1+‖x‖^q)|f(x)| ≤ p_(0,0)(f)+p_(q,0)(f)`

and from `0≤W_p≤4` deduces

`|S_P(f,U)| ≤ 4 [∑_p |w_p|/(1+‖x_p‖^q)] (p_(0,0)+p_(q,0))(f)`.

It then derives the same bound uniformly for any entire regulator family
provided the explicit **weighted lattice quadrature majorant**

`sup_{reg}∑_p |w_(reg,p)|/(1+‖x_(reg,p)‖^q)≤C`

holds. The model-dependent geometric cubature bound is NOT PROVED by this
module and remains an independently stated Wilson-lattice input.

No `sorry`, no axiom, no model-spectrum statement, no claims of completed
Original30/34/42. The conditional 34/39 original manuscript ledger remains
unchanged. Actual composite Wilson words, normalized smearing and the
precise 21-root inverse-transpose source cocycle still need identification.

## 4D periodic SU(2) fixed-box cubature (next CI target)

For the **actual six oriented plaquette types** per lattice site of a
four-dimensional periodic N-by-N-by-N-by-N box, the flattened source index
is `Fin6 × Fin(N⁴)`. The bare Wilson smearing uses the true lattice
four-volume weight `a⁴` per plaquette.

Whenever `a ≥ 0` and `N a ≤ R`, the number of positive plaquettes
is exactly `6 N⁴`, hence *without any external geometric input*
the finite weighted sum is bounded by

`∑_p a⁴/(1+‖x_p‖^q) ≤ 6 R⁴`.

Combining the genuine weighted Schwartz/Wilson estimate gives

`|S_P(f,U)| ≤ 24 R⁴ (p_(0,0)+p_(q,0))(f)`

uniformly in UV spacing, cutoff index, plaquette holonomies and sample
positions. This result concerns a **fixed physical box radius** R;
it is not a global infinite-volume bound (R→∞), nor is the cumulative
renormalized 21D source map controlled by this argument.
