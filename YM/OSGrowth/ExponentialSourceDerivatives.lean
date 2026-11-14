import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Analytic.IteratedFDeriv

set_option autoImplicit false
noncomputable section

namespace YMUIC.OSGrowth

/-- Exact all-order derivatives of an exponential linear source in a
commutative Banach algebra, followed by a continuous linear expectation.
The product identity is derived from the exponential power series. -/
theorem exponential_linear_source_derivatives
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (source : E →L[ℂ] A) (expectation : A →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun J => expectation (NormedSpace.exp (source J))) Set.univ ∧
    ∀ (r : ℕ) (h : Fin r → E),
      iteratedFDeriv ℂ r (fun J => expectation (NormedSpace.exp (source J))) 0 h =
        expectation (∏ j, source (h j)) := by
  have hexp : AnalyticOnNhd ℂ (NormedSpace.exp : A → A) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  have hsource : AnalyticOnNhd ℂ
      (fun J => NormedSpace.exp (source J)) Set.univ := by
    intro J _
    exact (NormedSpace.exp_analytic (source J)).comp (source.analyticAt J)
  refine ⟨fun J _ => (expectation.analyticAt _).comp (hsource J (Set.mem_univ J)), ?_⟩
  intro r h
  have hbase (v : Fin r → A) :
      iteratedFDeriv ℂ r (NormedSpace.exp : A → A) 0 v = ∏ j, v j := by
    rw [(NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℂ) (𝔸 := A)).iteratedFDeriv_eq_sum_of_completeSpace]
    have he (σ : Equiv.Perm (Fin r)) :
        NormedSpace.expSeries ℂ A r (fun j => v (σ j)) =
          ((r.factorial : ℂ)⁻¹) • ∏ j, v j := by
      simp only [NormedSpace.expSeries, smul_apply,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
      rw [Equiv.prod_comp σ v]
    simp_rw [he]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast Nat.factorial_ne_zero r
  change iteratedFDeriv ℂ r
    (expectation ∘ (fun J => NormedSpace.exp (source J))) 0 h = _
  rw [expectation.iteratedFDeriv_comp_left
    (hsource.contDiff.contDiffAt) (le_refl (r : WithTop ℕ∞))]
  change expectation (iteratedFDeriv ℂ r (NormedSpace.exp ∘ source) 0 h) = _
  rw [source.iteratedFDeriv_comp_right hexp.contDiff 0 (le_refl (r : WithTop ℕ∞)),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  rw [hbase]

end YMUIC.OSGrowth
