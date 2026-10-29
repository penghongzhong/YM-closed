import PublicC30.WilsonSchwartzCLM

set_option autoImplicit false

namespace YMUIC.OSTensor
open YMUICV128.Section03

/-- Genuine finite support cardinality controlled by an explicit *injective*
map into the local four-dimensional periodic coordinate chart.
Unlike an abstract cardinality bound, the exact local indexing map is an
argument, and its injectivity is machine-checked. -/
theorem localPlaquette_card_from_chart
    {N M : ℕ} (S : Finset (Periodic4DPlaquette N))
    (encode : {p : Periodic4DPlaquette N // p ∈ S} ↪
      Periodic4DPlaquette M) :
    (S.card : ℝ) ≤ 6 * (M : ℝ) ^ 4 := by
  classical
  have hc : S.card ≤ Fintype.card (Periodic4DPlaquette M) := by
    calc
      S.card =
          Fintype.card {p : Periodic4DPlaquette N // p ∈ S} := by simp
      _ ≤ Fintype.card (Periodic4DPlaquette M) :=
        Fintype.card_le_of_injective encode encode.injective
  have hr : (S.card : ℝ) ≤
      (Fintype.card (Periodic4DPlaquette M) : ℝ) := by
    exact_mod_cast hc
  simpa [Periodic4DPlaquette] using hr

/-- A local coordinate chart of physical side R controls all Wilson-root
plaquette sources whose supports admit this chart, independently of the
overall periodic regulator size N. The chart injection is a genuine
outstanding geometric obligation and is not hidden as a source estimate. -/
theorem localPlaquette_SchwartzCLM_uniform
    (N M : ℕ) (S : Finset (Periodic4DPlaquette N))
    (encode : {p : Periodic4DPlaquette N // p ∈ S} ↪
      Periodic4DPlaquette M)
    (U : Periodic4DPlaquette N → SU2)
    (position : Periodic4DPlaquette N → EuclideanSpace ℝ (Fin 4))
    (a R : ℝ) (ha : 0 ≤ a) (hlocal : a * (M : ℝ) ≤ R)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ) :
    ‖wilsonPlaquetteSchwartzCLM S U position a f‖ ≤
      24 * R ^ 4 * (SchwartzMap.seminorm ℝ 0 0) f := by
  have hc := localPlaquette_card_from_chart S encode
  have hp : (a ^ 4) * (S.card : ℝ) ≤ 6 * R ^ 4 := by
    have hpow : (a * (M : ℝ)) ^ 4 ≤ R ^ 4 :=
      pow_le_pow_left₀ (by positivity) hlocal 4
    calc
      a ^ 4 * (S.card : ℝ) ≤
          a ^ 4 * (6 * (M : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 6 * (a * (M : ℝ)) ^ 4 := by ring
      _ ≤ 6 * R ^ 4 := by nlinarith [hpow]
  have h := wilsonPlaquetteSchwartz_uniform_bound
    S U position a (6 * R ^ 4) ha hp f
  rw [wilsonPlaquetteSchwartzCLM_apply]
  calc
    _ ≤ (4 * (6 * R ^ 4)) * (SchwartzMap.seminorm ℝ 0 0) f := h
    _ = 24 * R ^ 4 * (SchwartzMap.seminorm ℝ 0 0) f := by ring

end YMUIC.OSTensor
