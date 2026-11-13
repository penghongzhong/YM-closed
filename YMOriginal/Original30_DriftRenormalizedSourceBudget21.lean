import YMOriginal.Original30_SourceCocycleBudget21
import YM.Wilson.DriftLeftOrderedRG21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- U3 inverse-coupling drift plus an O(g_j^4) corrected source residual
produces a cutoff-uniform actual Wilson-template budget for all 21
renormalized source channels.  This is the quantitative bridge from the
finite-dimensional source cocycle to the all-volume Original30 source
estimate. -/
theorem drift_controlled_renormalized_source_budget21
    {W T : Type*} [Fintype T]
    (N : ℕ)
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
    (words : TrueSpatialSources RootFiber21 N → T → List (List W))
    (coeff : TrueSpatialSources RootFiber21 N → T → ℂ)
    (Kbare : ℝ) (hKbare : 0 ≤ Kbare)
    (hbase : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ Kbare) :
    ∀ n ≤ Kstop, ∀ p : TrueSpatialSources RootFiber21 N,
      actualWilsonPolynomialBudget
        (fun bt : RootFiber21 × T =>
          words (bt.1, p.2) bt.2)
        (fun bt : RootFiber21 × T =>
          leftOrderedSourceRGChain R n bt.1 p.1 *
            coeff (bt.1, p.2) bt.2) ≤
      Kbare * Real.exp (C / (drift * xweak)) := by
  intro n hn p
  have hcol : ∀ α : RootFiber21,
      (∑ i : RootFiber21,
        ‖leftOrderedSourceRGChain R n i α‖) ≤
        Real.exp (C / (drift * xweak)) :=
    drift_controlled_left_rg_uniform
      R x Kstop xweak drift C
      hxweak hdrift hC hlower hstepX hresidual n hn
  exact mixed_spatial_root_budget21
    N (leftOrderedSourceRGChain R n)
    words coeff Kbare (Real.exp (C / (drift * xweak)))
    hKbare hbase hcol p

#print axioms drift_controlled_renormalized_source_budget21

end YMUIC.Original30
