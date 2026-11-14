import YMOriginal.Original30_DriftRenormalizedSourceBudget21
import YMOriginal.Original30_FiniteSpeciesAllVolume

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- The full deterministic joint-test consequence of the corrected 21-source
RG residual estimate.  No analytic source radius or final Schwinger growth
bound is assumed. -/
theorem drift_controlled_renormalized_joint_all_volume21
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (R : ℕ → SourceRGMatrix21)
    (x : ℕ → ℝ) (Kstop : ℕ)
    (xweak drift C : ℝ)
    (hxweak : 0 < xweak) (hdrift : 0 < drift) (hC : 0 ≤ C)
    (hlower : ∀ j ≤ Kstop, xweak ≤ x j)
    (hstepX : ∀ j < Kstop, drift ≤ x j - x (j + 1))
    (hresidual : ∀ j < Kstop, ∀ α : RootFiber21,
      (∑ i : RootFiber21,
        ‖R j i α - sourceCocycleIdentity i α‖) ≤
        C * ((x j)⁻¹ * (x j)⁻¹))
    (U : TrueSpatialSources RootFiber21 N → W → SU2)
    (words : TrueSpatialSources RootFiber21 N → T → List (List W))
    (coeff : TrueSpatialSources RootFiber21 N → T → ℂ)
    (Kbare : ℝ) (hKbare : 0 ≤ Kbare)
    (hbase : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ Kbare)
    (n : ℕ) (hn : n ≤ Kstop)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualWordJointCutoff r
      (fun _ : TrueSpatialSources RootFiber21 N => ((a ^ 4 : ℝ) : ℂ))
      U
      (fun p bt : RootFiber21 × T =>
        words (bt.1, p.2) bt.2)
      (fun p bt : RootFiber21 × T =>
        leftOrderedSourceRGChain R n bt.1 p.1 *
          coeff (bt.1, p.2) bt.2)
      (actualJointSpeciesPosition a) f‖ ≤
      (4096 * (Fintype.card RootFiber21 : ℝ) *
        (Kbare * Real.exp (C / (drift * xweak)))) ^ r *
      (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  have hKren : 0 ≤ Kbare * Real.exp (C / (drift * xweak)) :=
    mul_nonneg hKbare (Real.exp_pos _).le
  have hbudget : ∀ p : TrueSpatialSources RootFiber21 N,
      actualWilsonPolynomialBudget
        (fun bt : RootFiber21 × T =>
          words (bt.1, p.2) bt.2)
        (fun bt : RootFiber21 × T =>
          leftOrderedSourceRGChain R n bt.1 p.1 *
            coeff (bt.1, p.2) bt.2) ≤
        Kbare * Real.exp (C / (drift * xweak)) :=
    drift_controlled_renormalized_source_budget21
      N R x Kstop xweak drift C
      hxweak hdrift hC hlower hstepX hresidual
      words coeff Kbare hKbare hbase n hn
  exact actual_word_joint_finite_species_all_volume_bound
    r N a ha ha1 U
    (fun p bt : RootFiber21 × T =>
      words (bt.1, p.2) bt.2)
    (fun p bt : RootFiber21 × T =>
      leftOrderedSourceRGChain R n bt.1 p.1 *
        coeff (bt.1, p.2) bt.2)
    (Kbare * Real.exp (C / (drift * xweak)))
    hKren hbudget f

#print axioms drift_controlled_renormalized_joint_all_volume21

end YMUIC.Original30
