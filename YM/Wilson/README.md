# Original30: genuine SU(2) Wilson root source norm bridge

This public branch extends the already-verified Original30 Fourier/Schwartz
sources, without modifying the main repository branch or publishing a paper.

**Actual mathematical source, no model surrogates**:
- The root is `W_p(U)=2-Re Tr(U_p)`, where `U_p` is an actual
  `Matrix.specialUnitaryGroup (Fin 2) ℂ` value.
- `RootBound.lean` is an unchanged Git blob of the project's original
  Wilson root bound.
- Each root is sampled at an arbitrary physical location `x_p ∈ ℝ⁴`,
  with `h_f(p;U)=f(x_p) W_p(U)` for an actual complex Schwartz test `f`.
- Derived pointwise and finite `ℓ∞` bounds: `‖h_f‖∞ ≤ 4 p_(0,0)(f)`,
  with **no factor depending on the number of plaquettes**.
- The same bound holds simultaneously for arbitrary lattice cutoff and
  volume indexing. The source map is Lipschitz in the test.

**21-dimensional source renormalization**:
- A root-mixing matrix `B_{jα}` produces
  `h'_(f,α)=∑_{j=1}^{21} B_{jα} h_(f,j)`.
- Exact finite sum estimate:
  `‖h'_f‖∞ ≤ 4 (sup_α ∑_j |B_{jα}|) p_(0,0)(f)`.
- An order-independent bound `sup_α ∑_j |B_{jα}| ≤ K` is a **hypothesis
  for the renormalized conclusion**, never an axiom or an asserted result.

**Important separation between OS positivity and OS growth**:
An arbitrary invertible finite-dimensional source basis change preserves
positive-semidefinite reflection Gram matrices `B* G B ≥ 0` even if
`‖B‖` is arbitrarily large. The *uniform* OS E0prime factorial distribution
bounds do **not** follow without controlling source amplification. For
example, `B_n=2^n I_21` is invertible, but its column norm is `2^n`.
This is not an actual YM counterexample; it demonstrates that invertibility
and positivity alone cannot supply the missing uniform constant.

**Still open for manuscript Original30 (34/39 remains unchanged)**:
1. Identify the v108/v118 normalized/frozen source with this exact
   plaquette-test vector, including a-dependent multipliers, root templates,
   21-dimensional cocycle, and Jacobian/normalization factors.
2. Derive the actual cumulative matrix column bound `K` (or a weaker
   direct source norm estimate) from RG/polymer estimates, uniformly in
   `a,Λ,RG` and chart/root index; it cannot be assumed without source.
3. Construct 4r-variable smooth joint periodization with the verified
   multi-coordinate C² Fourier derivative chain and exact coefficient
   source factorization.
4. Close the exact original E0prime factorial Schwartz/test hypotheses.
5. I7 remains open, as do original environments 1,24,30,34,42.

The new theorem would certify only the actual **bare SU(2) source bound**
and its exact 21-root linear-cocycle amplification formula. It does not
certify that the physical renormalized Yang–Mills source realizes that
cocycle or that its norm is regulator-uniform.

## RG cocycle composition (formal check pending)

For two actual finite root-fiber changes `B,C : Fin21 × Fin21 → ℂ`,
construct `(BC)_{jα}=∑_β B_{jβ} C_{βα}`. The new Lean module derives
the exact action on the same Wilson plaquette-source vector, proves
submultiplicativity of column sums, and deduces

`‖h_{BC,f}‖∞ ≤ 4 K_B K_C p_(0,0)(f)`.

For an RG ladder this suggests the sufficient **quantitative goal**:
if step matrices have `K_j ≤ 1+δ_j` and the regulator-uniform sum
`∑_j δ_j ≤ M` holds, the cumulative source amplification can be bounded
by `exp M`. This goal is *not proved here* and certainly does not follow
from invertibility, PSD preservation, or the number 21 alone.
