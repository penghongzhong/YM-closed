import YM.Wilson.WeightedSmearing

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson

/-- One canonical orientation for each of the six positive plaquette types
at each of the N⁴ lattice sites of a four-dimensional periodic box. -/
abbrev WilsonBoxPlaquettes (N : ℕ) := Fin 6 × Fin (N ^ 4)

/-- For a 4D N-site-per-axis physical box with lattice spacing a and
N*a ≤ R, the actual plaquette cubature weights a⁴ have a volume-uniform
weighted majorant. The bound applies to ANY placement function, and
therefore to the actual lattice plaquette positions. -/
theorem wilson_box_weighted_sum_bound
    (N : ℕ) (a R : ℝ) (ha : 0 ≤ a) (_hR : 0 ≤ R)
    (hbox : (N : ℝ) * a ≤ R)
    (position : WilsonBoxPlaquettes N → Space4) (q : ℕ) :
    (∑ p : WilsonBoxPlaquettes N,
      ‖((a ^ 4 : ℝ) : ℂ)‖ / (1 + ‖position p‖ ^ q)) ≤
      6 * R ^ 4 := by
  have hp (p : WilsonBoxPlaquettes N) :
      ‖((a ^ 4 : ℝ) : ℂ)‖ / (1 + ‖position p‖ ^ q) ≤ a ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ha 4)]
    have hdenom : 0 < 1 + ‖position p‖ ^ q := by positivity
    apply (div_le_iff₀ hdenom).mpr
    have hpow : 0 ≤ ‖position p‖ ^ q := by positivity
    have ha4 : 0 ≤ a ^ 4 := pow_nonneg ha 4
    nlinarith
  have hlen : 0 ≤ (N : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
  have hvolume : ((N : ℝ) * a) ^ 4 ≤ R ^ 4 :=
    pow_le_pow_left₀ hlen hbox 4
  calc
    (∑ p : WilsonBoxPlaquettes N,
      ‖((a ^ 4 : ℝ) : ℂ)‖ / (1 + ‖position p‖ ^ q)) ≤
        ∑ _p : WilsonBoxPlaquettes N, a ^ 4 := by
      apply Finset.sum_le_sum
      intro p hmem
      exact hp p
    _ = 6 * ((N : ℝ) * a) ^ 4 := by
      simp [WilsonBoxPlaquettes, Fintype.card_prod]
      ring
    _ ≤ 6 * R ^ 4 :=
      mul_le_mul_of_nonneg_left hvolume (by norm_num)

/-- Exact finite 4D SU(2) Wilson plaquette source smearing over N⁴ sites.
This derives the needed weighted source sum for each fixed physical box;
no source-weight norm bound is assumed. -/
theorem wilson_box_source_bound
    (N : ℕ) (a R : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hbox : (N : ℝ) * a ≤ R)
    (U : WilsonBoxPlaquettes N → YMUICV128.Section03.SU2)
    (position : WilsonBoxPlaquettes N → Space4)
    (f : SchwartzMap Space4 ℂ) (q : ℕ) :
    ‖wilsonWeightedSmearing (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U position f‖ ≤
      24 * R ^ 4 *
        (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ q 0 f) := by
  have hC : 0 ≤ 6 * R ^ 4 := by positivity
  have hw := wilson_weighted_smearing_bound
    (fun _ : WilsonBoxPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
    U position f q (6 * R ^ 4) hC
    (wilson_box_weighted_sum_bound N a R ha hR hbox position q)
  convert hw using 1; ring

/-- One physical box size R serves every UV cutoff, lattice spacing and
volume regulator of the same finite 4D Wilson cube family. -/
theorem wilson_box_source_uniform_across_cutoffs
    {Regulator : Type*}
    (N : Regulator → ℕ) (a : Regulator → ℝ) (R : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hR : 0 ≤ R)
    (hbox : ∀ i, (N i : ℝ) * a i ≤ R)
    (U : (i : Regulator) → WilsonBoxPlaquettes (N i) →
      YMUICV128.Section03.SU2)
    (position : (i : Regulator) → WilsonBoxPlaquettes (N i) → Space4)
    (f : SchwartzMap Space4 ℂ) (q : ℕ) :
    ∀ i, ‖wilsonWeightedSmearing
      (fun _ : WilsonBoxPlaquettes (N i) => (((a i) ^ 4 : ℝ) : ℂ))
        (U i) (position i) f‖ ≤
      24 * R ^ 4 *
        (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ q 0 f) := by
  intro i
  exact wilson_box_source_bound (N i) (a i) R (ha i) hR (hbox i)
    (U i) (position i) f q

end YMUIC.Wilson
