import YMOriginal.Original24_TwoRootMayerSeries
import YMOriginal.Original24_PublishedPenroseOnActualGraph

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Original24: full physical TWO-ROOT finite Penrose weighted majorant

Combine the LITERAL n+1-history connected Mayer coefficient with
the UNIVERSAL published finite hard-core Penrose tree graph
inequality. Both the two actual root contacts and the 1/(n+1)!
label symmetry divisor are retained exactly; the output is a
positive spanning-TREE weighted activity sum, not an abstract
hPenrose input on unknown cluster coefficients.

Remaining (not claimed in this module): summing the concrete
spanning-tree majorant over ALL n by the physical FP iteration,
the true Balaban CMP R-history model dictionary, and fixed-D
counterterms. The existing U2 KP iteration is separately verified.
-/

/-- EXACT finite positive tree series corresponding to the literal
two-root hard-core connected Mayer sum, with full label factorial. -/
def actualTwoRootSpanningTreeMajorant
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) : ℝ := by
  classical
  exact (Nat.factorial (n + 1) : ℝ)⁻¹ *
    ∑ tuple : Fin (n + 1) → Γ,
      if actualTwoRootPhysicalContact n N chi rootP rootQ support tuple then
        ((actualHardCoreSpanningTrees n
          (actualPeriodicLabeledHardCoreGraph (n + 1) N chi
            support tuple)).card : ℝ) *
          (∏ i : Fin (n + 1), ‖z (tuple i)‖)
      else 0

/-- No arbitrary cluster-coefficient-specific Penrose assumption:
the published UNIVERSAL graph result is instantiated on each
fully explicit physical labeled history graph, then summed with
the EXACT actual Bałaban activity weights and factorial.

The result is the first really weighted finite-history bridge
on the shortest Original24 proof chain. -/
theorem actual_two_root_hardcore_penrose_weighted
    (Pub : PublishedPenroseHardCoreTreeBound)
    {Γ : Type*} [Fintype Γ]
    (n N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) :
    ‖actualTwoRootHardCoreMayerTerm n N chi rootP rootQ support z‖ ≤
      actualTwoRootSpanningTreeMajorant n N chi rootP rootQ support z := by
  classical
  let factor : ℝ := (Nat.factorial (n + 1) : ℝ)⁻¹
  let part : (Fin (n + 1) → Γ) → ℂ := fun tuple =>
    if actualTwoRootPhysicalContact n N chi rootP rootQ support tuple then
      (actualPeriodicConnectedMayerCoefficient n N chi support tuple : ℂ) *
        (∏ i : Fin (n + 1), z (tuple i))
    else 0
  let bound : (Fin (n + 1) → Γ) → ℝ := fun tuple =>
    if actualTwoRootPhysicalContact n N chi rootP rootQ support tuple then
      ((actualHardCoreSpanningTrees n
        (actualPeriodicLabeledHardCoreGraph (n + 1) N chi
          support tuple)).card : ℝ) *
        (∏ i : Fin (n + 1), ‖z (tuple i)‖)
    else 0
  have hFac : 0 ≤ factor := by
    dsimp [factor]
    positivity
  have hFacNorm :
      ‖((Nat.factorial (n + 1) : ℂ)⁻¹)‖ = factor := by
    simp [factor]
  have hterm (tuple : Fin (n + 1) → Γ) :
      ‖part tuple‖ ≤ bound tuple := by
    dsimp [part, bound]
    by_cases hContact :
        actualTwoRootPhysicalContact n N chi rootP rootQ support tuple
    · simp only [if_pos hContact, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, norm_prod]
      have hT := actual_periodic_mayer_penrose_tree_bound
        Pub n N chi support tuple
      exact mul_le_mul_of_nonneg_right hT
        (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    · simp [hContact]
  have hsum :
      ‖∑ tuple : Fin (n + 1) → Γ, part tuple‖ ≤
        ∑ tuple : Fin (n + 1) → Γ, bound tuple := by
    calc
      ‖∑ tuple : Fin (n + 1) → Γ, part tuple‖ ≤
          ∑ tuple : Fin (n + 1) → Γ, ‖part tuple‖ :=
        norm_sum_le _ _
      _ ≤ ∑ tuple : Fin (n + 1) → Γ, bound tuple :=
        Finset.sum_le_sum (fun tuple _ => hterm tuple)
  change ‖((Nat.factorial (n + 1) : ℂ)⁻¹) *
    (∑ tuple : Fin (n + 1) → Γ, part tuple)‖ ≤
      factor * (∑ tuple : Fin (n + 1) → Γ, bound tuple)
  rw [norm_mul, hFacNorm]
  exact mul_le_mul_of_nonneg_left hsum hFac

/-- The two sectors literally use the ORIGINAL old/new-R coefficients
at the SAME j, background and physical graph. No independent
marked connected-cluster bound is inserted. -/
theorem actual_balaban_old_new_two_root_penrose_weighted
    (Pub : PublishedPenroseHardCoreTreeBound)
    {Γ Ω : Type*} [Fintype Γ]
    (D : YMUICV128.Section02.U1Data Γ Ω)
    (j n N chi : ℕ) (omega : Ω)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N)) :
    (‖actualBalabanOldRTwoRootHardCoreTerm D j n N chi omega
        rootP rootQ support‖ ≤
      actualTwoRootSpanningTreeMajorant n N chi rootP rootQ
        support (fun X => D.oldR j X omega)) ∧
    (‖actualBalabanNewRTwoRootHardCoreTerm D j n N chi omega
        rootP rootQ support‖ ≤
      actualTwoRootSpanningTreeMajorant n N chi rootP rootQ
        support (fun X => D.newR j X omega)) := by
  exact ⟨
    actual_two_root_hardcore_penrose_weighted Pub n N chi
      rootP rootQ support (fun X => D.oldR j X omega),
    actual_two_root_hardcore_penrose_weighted Pub n N chi
      rootP rootQ support (fun X => D.newR j X omega)⟩

end YMUIC.Original24
