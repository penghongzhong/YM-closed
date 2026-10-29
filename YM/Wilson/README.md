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

## A genuinely sufficient per-RG-step summability criterion (Lean target)

Let `C_j` be the actual ordered `21×21` source cocycle matrices.
If for every step and root column,
`∑_k |C_j(k,α)| ≤ 1 + δ_j`, `δ_j ≥ 0`, and
`sup_m ∑_{j<m} δ_j ≤ M`, then the proved matrix-cocycle
column submultiplicativity and the standard exponential product inequality
yield the derived (not assumed) *cumulative* source estimate

`‖h_{C_0···C_{m-1}, f}‖∞ ≤ 4 exp(M) p_(0,0)(f)`

for every finite RG length `m`, every SU2 plaquette configuration, every
root placement, and every compact or noncompact Schwartz test `f`.

This replaces the earlier **cumulative** bound hypothesis with **per-step**
bounds and a summable error budget. The latter two remain genuine Yang–Mills
RG obligations. The argument is not a proof of Original30 or I7 until those
per-step bounds and the v108/v118 source dictionary are established.

## C29: direct one-step source defect instead of an assumed step norm

The extra certificate `SourceDefect21.lean` proves that, for an
**actual matrix entrywise difference**, the column estimate

`∑_j ‖C_n(j,α)-δ_(jα)‖ ≤ d_n`

implies `‖C_n‖_(col,1) ≤ 1+d_n`. For a uniform nonnegative
summable sequence `d_n`, the existing full cocycle theorem then yields

`‖h_(C_(n-1)…C_0,f)‖∞ ≤ 4 exp(∑_n d_n) p_(0,0)(f)`,

including varying regulator and volume indices. This is a Lean
conditional implication; **no actual Yang–Mills one-step B09 RG source
defect or its summability is assumed to be proved**. In the paper,
the physical dual source evolves by inverse transpose, which still
requires a precise correspondence with `C_n`.

The prior manuscript **34/39** ledger and unresolved IDs are unchanged.

## Dual/inverse-transpose source cocycle (new strict Lean target)

The paper's actual renormalized source coordinates obey
`Jhat = Z_m^{-T} J_0`, rather than the primal `Z_m`.
The new modules `DualSourceInverse21.lean` and
`DualSourceRGUniform21.lean` use the exact finite-dimensional
identity `(I+A_j^T) B_j=I`, with `B_j=(I+A_j)^{-T}`
where the inverse exists.

The true **primal row** estimate `∀β:∑_k|A_j(β,k)|≤δ_j<1`
is proved to imply the **dual column** estimate
`∀α:∑_k|B_j(k,α)|≤1/(1−δ_j)`.
If `0≤δ_j≤1/2`, this is at most `1+2δ_j`.

Under the separate, genuine RG model task
`sup_m ∑_{j<m} δ_j ≤ M`, the cumulative dual source satisfies

`sup_m‖h_{B_0···B_{m−1},f}‖∞≤4 exp(2M) p_(0,0)(f)`.

The proof **does not assume** the inverse norm bound or the cumulative
norm bound. It **does assume** the exact primal/dual inverse identity
and a summable physical RG step error budget; it has not derived
these from Balaban's RG, the physical canonical `M_D^(0)`, source
normalization or Wilson polynomial roots. In particular a one-step
`δ_j≤1/2` alone is insufficient.

This closes the previously ambiguous `Z^{-T}` orientation *within
the finite 21-dimensional algebraic interface*, not Original30 itself.

## Geometric RG source error: quantitative conditional corollary

The auxiliary `SourceGeometric21` (after CI) uses only the concrete
`\sum_{j=1}^{21}|A_{n,βj}| \le D\theta^n`, `0≤θ<1`,
`0≤D≤1/2`, and the exact dual inverse equation. It constructs
the previously assumed summability/partial-sum bound, yielding
`‖h_f^(n)‖∞ ≤ 4 exp(2D/(1−θ)) p_(0,0)(f)` for all scales and
cutoff-volume regulators. Crucially the geometric decay premise
is NOT implied by the paper's one-step estimate `‖A_n‖≤1/2`;
model matching is OPEN. No new original environment is counted.
