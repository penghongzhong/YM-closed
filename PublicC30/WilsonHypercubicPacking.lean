import PublicC30.WilsonPlaquetteSmearing

set_option autoImplicit false

namespace YMUIC.OSTensor
open YMUICV128.Section03

/-- Six unoriented plaquette planes at each vertex in a four-dimensional
periodic hypercubic box with N sites in each of its four directions. -/
abbrev Periodic4DPlaquette (N : ℕ) := Fin 6 × (Fin 4 → Fin N)

/-- The six plaquette orientations give an *actual* finite combinatorial
count, so no abstract cutoff/volume counting hypothesis is needed. -/
theorem periodic4D_plaquette_card
    (N : ℕ) (S : Finset (Periodic4DPlaquette N)) :
    (S.card : ℝ) ≤ 6 * (N : ℝ) ^ 4 := by
  classical
  have hs : S.card ≤ Fintype.card (Periodic4DPlaquette N) :=
    Finset.card_le_univ S
  have hfull : Fintype.card (Periodic4DPlaquette N) = 6 * N ^ 4 := by
    simp [Periodic4DPlaquette]
  have hr : (S.card : ℝ) ≤
      (Fintype.card (Periodic4DPlaquette N) : ℝ) := by
    exact_mod_cast hs
  simpa only [hfull, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hr

/-- With spacing a and physical box length bounded by L, the actual
unoriented-plaquette weighted count is at most 6 L⁴, for every N. -/
theorem periodic4D_physical_plaquette_count
    (N : ℕ) (S : Finset (Periodic4DPlaquette N))
    (a L : ℝ) (ha : 0 ≤ a)
    (hbox : a * (N : ℝ) ≤ L) :
    a ^ 4 * (S.card : ℝ) ≤ 6 * L ^ 4 := by
  have hc := periodic4D_plaquette_card N S
  have hmesh : 0 ≤ a * (N : ℝ) := by positivity
  have hp : (a * (N : ℝ)) ^ 4 ≤ L ^ 4 :=
    pow_le_pow_left₀ hmesh hbox _
  calc
    a ^ 4 * (S.card : ℝ) ≤
        a ^ 4 * (6 * (N : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 6 * (a * (N : ℝ)) ^ 4 := by ring
    _ ≤ 6 * L ^ 4 := by nlinarith [hp]

/-- A genuine SU(2) Wilson plaquette source on the entire four-dimensional
periodic regulator, not an arbitrary abstract Wilson source map.

The physical size L, rather than cutoff N or spacing a, controls its
complex Schwartz seminorm. The estimate holds for *every* gauge
configuration U, set of sampled plaquettes and embedding position. -/
theorem periodic4D_wilson_Schwartz_uniform
    (N : ℕ) (S : Finset (Periodic4DPlaquette N))
    (U : Periodic4DPlaquette N → SU2)
    (position : Periodic4DPlaquette N → EuclideanSpace ℝ (Fin 4))
    (a L : ℝ) (ha : 0 ≤ a) (hbox : a * (N : ℝ) ≤ L)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    ‖wilsonPlaquetteSchwartzSmear S U position a f‖ ≤
      24 * L ^ 4 * (SchwartzMap.seminorm ℝ 0 0) f := by
  have hpack := periodic4D_physical_plaquette_count N S a L ha hbox
  have h := wilsonPlaquetteSchwartz_uniform_bound
    S U position a (6 * L ^ 4) ha hpack f
  calc
    _ ≤ (4 * (6 * L ^ 4)) * (SchwartzMap.seminorm ℝ 0 0) f := h
    _ = 24 * L ^ 4 * (SchwartzMap.seminorm ℝ 0 0) f := by ring

end YMUIC.OSTensor
