import YMOriginal.Original30_FiniteSpeciesAllVolume
import YM.Wilson.SourceCocycle21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- Flatten the 21 bare source channels into one mixed output channel. -/
def mixedRootWords21
    {W T : Type*} [Fintype T]
    (words : RootFiber21 → T → List (List W))
    (_α : RootFiber21) :
    (RootFiber21 × T) → List (List W)
  | (β, t) => words β t

/-- Coefficients of the same flattened mixed output channel. -/
def mixedRootCoeff21
    {T : Type*} [Fintype T]
    (B : RootFiber21 → RootFiber21 → ℂ)
    (coeff : RootFiber21 → T → ℂ)
    (α : RootFiber21) :
    (RootFiber21 × T) → ℂ
  | (β, t) => B β α * coeff β t

/-- Exact polynomial identity: source-matrix mixing is literally a finite
linear combination of the 21 bounded Wilson polynomial channels. -/
theorem actual_wilson_polynomial_mixed_root_identity
    {W T : Type*} [Fintype T]
    (U : W → SU2)
    (B : RootFiber21 → RootFiber21 → ℂ)
    (words : RootFiber21 → T → List (List W))
    (coeff : RootFiber21 → T → ℂ)
    (α : RootFiber21) :
    actualWilsonPolynomial U
      (mixedRootWords21 words α) (mixedRootCoeff21 B coeff α) =
      ∑ β : RootFiber21,
        B β α * actualWilsonPolynomial U (words β) (coeff β) := by
  classical
  unfold actualWilsonPolynomial mixedRootWords21 mixedRootCoeff21
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Column l1 control of the source cocycle gives an explicit uniform
finite-template budget for every mixed output channel. -/
theorem mixed_root_polynomial_budget_le
    {W T : Type*} [Fintype T]
    (B : RootFiber21 → RootFiber21 → ℂ)
    (words : RootFiber21 → T → List (List W))
    (coeff : RootFiber21 → T → ℂ)
    (K KB : ℝ) (hK : 0 ≤ K)
    (hbase : ∀ β,
      actualWilsonPolynomialBudget (words β) (coeff β) ≤ K)
    (hcol : ∀ α,
      (∑ β : RootFiber21, ‖B β α‖) ≤ KB)
    (α : RootFiber21) :
    actualWilsonPolynomialBudget
      (mixedRootWords21 words α) (mixedRootCoeff21 B coeff α) ≤
      K * KB := by
  classical
  unfold actualWilsonPolynomialBudget mixedRootWords21 mixedRootCoeff21
  rw [Fintype.sum_prod_type]
  calc
    (∑ β : RootFiber21, ∑ t : T,
      ‖B β α * coeff β t‖ * (4 : ℝ) ^ (words β t).length) =
      ∑ β : RootFiber21,
        ‖B β α‖ *
          actualWilsonPolynomialBudget (words β) (coeff β) := by
      apply Finset.sum_congr rfl
      intro β hβ
      unfold actualWilsonPolynomialBudget
      simp only [norm_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ ∑ β : RootFiber21, ‖B β α‖ * K := by
      apply Finset.sum_le_sum
      intro β hβ
      exact mul_le_mul_of_nonneg_left (hbase β) (norm_nonneg _)
    _ = K * (∑ β : RootFiber21, ‖B β α‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ K * KB := mul_le_mul_of_nonneg_left (hcol α) hK

/-- Sitewise version used by the actual all-volume 21-species source.
The mixing matrix may depend on the RG reading scale but not on the
spatial volume. -/
theorem mixed_spatial_root_budget21
    {W T : Type*} [Fintype T]
    (N : ℕ)
    (B : RootFiber21 → RootFiber21 → ℂ)
    (words : TrueSpatialSources RootFiber21 N → T → List (List W))
    (coeff : TrueSpatialSources RootFiber21 N → T → ℂ)
    (K KB : ℝ) (hK : 0 ≤ K)
    (hbase : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (hcol : ∀ α,
      (∑ β : RootFiber21, ‖B β α‖) ≤ KB) :
    ∀ p : TrueSpatialSources RootFiber21 N,
      actualWilsonPolynomialBudget
        (fun bt : RootFiber21 × T =>
          words (bt.1, p.2) bt.2)
        (fun bt : RootFiber21 × T =>
          B bt.1 p.1 * coeff (bt.1, p.2) bt.2) ≤
        K * KB := by
  intro p
  let w : RootFiber21 → T → List (List W) :=
    fun β t => words (β, p.2) t
  let c : RootFiber21 → T → ℂ :=
    fun β t => coeff (β, p.2) t
  have hb : ∀ β, actualWilsonPolynomialBudget (w β) (c β) ≤ K := by
    intro β
    exact hbase (β, p.2)
  simpa [w, c, mixedRootWords21, mixedRootCoeff21] using
    mixed_root_polynomial_budget_le B w c K KB hK hb hcol p.1

end YMUIC.Original30
