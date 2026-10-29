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
