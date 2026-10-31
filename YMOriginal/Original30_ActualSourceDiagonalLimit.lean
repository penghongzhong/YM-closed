import YMOriginal.Original30_ActualSourceClusterHierarchy

set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- A concrete ultraviolet spacing. -/
def wilsonDiagonalSpacing (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

/-- A concrete lattice size with physical side length n+1. -/
def wilsonDiagonalSize (n : ℕ) : ℕ := (n + 1) ^ 2

/-- Simultaneous removal of the ultraviolet and volume regulators for the
bounded-coefficient actual Wilson source family. One ultrafilter carries
a -> 0, a*N -> infinity, and every full joint Schwartz moment to a normalized
continuous hierarchy with the same factorial estimate. No moment-limit or
regulator-limit premise is assumed. The limit is a cluster hierarchy of the
bare family; physical renormalization, full-net convergence and uniqueness
independent of the ultrafilter remain separate obligations. -/
theorem actual_source_diagonal_limit
    {Ω W : ℕ → Type*} {T : Type*} [Fintype T]
    [∀ n, TopologicalSpace (Ω n)] [∀ n, MeasurableSpace (Ω n)]
    [∀ n, OpensMeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (U : ∀ n, Ω n → TrueSpatialPlaquettes (wilsonDiagonalSize n) → W n → SU2)
    (words : ∀ n, TrueSpatialPlaquettes (wilsonDiagonalSize n) → T → List (List (W n)))
    (coeff : ∀ n, TrueSpatialPlaquettes (wilsonDiagonalSize n) → T → ℂ)
    (hU : ∀ n p w, Continuous (fun ω => U n ω p w))
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ n p, actualWilsonPolynomialBudget (words n p) (coeff n p) ≤ K) :
    ∃ u : Ultrafilter ℕ, (u : Filter ℕ) ≤ atTop ∧
      Tendsto wilsonDiagonalSpacing (u : Filter ℕ) (𝓝 0) ∧
      Tendsto (fun n => wilsonDiagonalSpacing n * (wilsonDiagonalSize n : ℝ))
        (u : Filter ℕ) atTop ∧
      ∃! H : YMUIC.Original34.SchwingerHierarchy,
        (∀ r f, Tendsto (fun n =>
          actualWilsonSourceJointDistribution (μ n)
            (fun _ => ((wilsonDiagonalSpacing n ^ 4 : ℝ) : ℂ))
            (U n) (words n) (coeff n) r
            (actualJointLatticePosition (wilsonDiagonalSpacing n)) f)
          (u : Filter ℕ) (𝓝 (H.S r f))) ∧
        (∀ f : YMUIC.Original34.JointTest 0, H.S 0 f = f 0) ∧
        ∀ r f, ‖H.S r f‖ ≤
          (2 * Real.exp (24576 * K)) * (r.factorial : ℝ) *
            YMUIC.OSTensor.jointSchwartzControl r (8 * r) (8 * r) f := by
  have ha (n : ℕ) : 0 < wilsonDiagonalSpacing n := by
    unfold wilsonDiagonalSpacing
    positivity
  have ha1 (n : ℕ) : wilsonDiagonalSpacing n ≤ 1 := by
    unfold wilsonDiagonalSpacing
    apply inv_le_one_of_one_le₀
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  obtain ⟨u, hu, hH⟩ := actual_source_cluster_hierarchy (atTop : Filter ℕ)
    μ wilsonDiagonalSize wilsonDiagonalSpacing ha ha1 U words coeff hU K hK hbudget
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hUV : Tendsto wilsonDiagonalSpacing atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hsize (n : ℕ) :
      wilsonDiagonalSpacing n * (wilsonDiagonalSize n : ℝ) = (n : ℝ) + 1 := by
    have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [wilsonDiagonalSpacing, wilsonDiagonalSize, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one]
    field_simp
  have hIR : Tendsto
      (fun n => wilsonDiagonalSpacing n * (wilsonDiagonalSize n : ℝ)) atTop atTop := by
    simpa only [hsize] using hn
  exact ⟨u, hu, hUV.mono_left hu, hIR.mono_left hu, hH⟩

end YMUIC.Original30
