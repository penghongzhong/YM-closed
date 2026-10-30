import YMOriginal.Original24_ExplicitTwoFugacityKP

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Original24: explicit O(aAct) full two-root tree bound from U1 and FP

The two-fugacity route corrects both structural problems in a
naively deleted second Wilson root:
(1) q is allowed arbitrary degree in the extended connected tree;
(2) the physical n=0 (zero bulk) term is excluded and the
    original O(aAct) factor is recovered via lambda ~ 1/aAct.

All source-dependent analytical estimates now follow from the
unmarked local U1 activity norm, a QUANTITATIVE weak-coupling
margin, and the already proved augmented periodic KP recursion.

The only additional input hFP below is the genuine published
positive FINITE-HEIGHT tree/forest enumeration comparison for
the exact tagged physical tree family, uniformly in its
two independent fugacities; it is NOT the desired O(aAct) bound.
A theorem matching the actual C29 n+2 Mayer trees to this
augmented finite-height family still must be established.
-/

/-- In the presence of the exact two-fugacity Fernández--Procacci
finite-height enumeration for real physical labeled trees, derive
the FINAL O(aAct) two-root tree bound with explicit constant,
without postulating its convergence or a completed root-tree sum.

No signed Ursell or original24 local jet/counterterm conclusion
appears as a theorem premise. -/
theorem original24_two_root_tree_O_aAct_from_U1_and_FP
    {Tree Γ : Type*}
    [DecidableEq Tree] [Fintype Γ]
    (N chi : ℕ)
    (rootP rootQ : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (haAct : 0 < aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall :
      4 * (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
        kappa - cGeo * mu)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        ‖z X‖ * Real.exp (kappa * (d X : ℝ))) ≤ aAct)
    (trees : ℕ → Finset Tree)
    (bulkCount qCount : Tree → ℕ)
    (weight : Tree → ℝ) (hweight : ∀ T, 0 ≤ weight T)
    (hFP :
      ∀ (lam eps : ℝ) (h : ℕ), 1 ≤ lam → 0 < eps →
        (∑ T ∈ trees h,
          weight T * lam ^ bulkCount T * eps ^ qCount T) ≤
        Real.exp
          (actualPeriodicFirstRootSum N chi rootP
            (actualSecondRootAugmentedSupport N support rootQ)
            (actualSecondRootAugmentedActivity
              (fun X => (lam : ℂ) * z X) eps)
            (actualSecondRootAugmentedSize d rootQ.card)
            cGeo mu h) - 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℕ,
        (∑ T ∈ (trees h).filter
          (fun T => 1 ≤ bulkCount T ∧ qCount T = 1),
            weight T) ≤ C * aAct := by
  let B : ℝ := (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ)
  let E : ℝ := Real.exp (kappa * (rootQ.card : ℝ))
  let delta : ℝ := kappa - cGeo * mu
  let M : ℝ :=
    Real.exp ((rootP.card : ℝ) * (delta / 2)) - 1
  let C : ℝ := M * (32 * B ^ 2 * E / delta ^ 2)
  have hM : 0 ≤ M := by
    dsimp [M]
    apply sub_nonneg.mpr
    apply Real.one_le_exp_iff.mpr
    have hroot : 0 ≤ (rootP.card : ℝ) := Nat.cast_nonneg _
    dsimp [delta]
    exact mul_nonneg hroot (by linarith [hdelta])
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hM (by positivity)
  obtain ⟨lam, eps, hlam, heps, hproduct, hforest⟩ :=
    original24_actual_double_fugacity_root_forest_from_U1
      N chi rootP rootQ support z d
      kappa mu cGeo aAct haAct hdelta hsize hsmall hLocalNorm
  let R : ℝ := 32 * B ^ 2 * E * aAct / delta ^ 2
  have hpositive : 0 < lam * eps :=
    mul_pos (by linarith [hlam] : 0 < lam) heps
  have hproductR : (lam * eps) * R = 1 := by
    simpa only [R, B, E, delta] using hproduct
  have hdenom : M / (lam * eps) = M * R := by
    apply (div_eq_iff₀ hpositive).mpr
    calc
      M = M * 1 := by ring
      _ = M * ((lam * eps) * R) := by rw [hproductR]
      _ = (M * R) * (lam * eps) := by ring
  have hreplace : M * R = C * aAct := by
    dsimp [C, R]
    ring
  refine ⟨C, hC, ?_⟩
  intro h
  have hcomplete :
      (∑ T ∈ trees h,
        weight T * lam ^ bulkCount T * eps ^ qCount T) ≤ M :=
    (hFP lam eps h hlam heps).trans (hforest h)
  have hmark :=
    one_q_nonempty_bulk_from_doped_majorant
      (trees h) bulkCount qCount weight hweight lam eps M
      hlam heps hcomplete
  calc
    (∑ T ∈ (trees h).filter
      (fun T => 1 ≤ bulkCount T ∧ qCount T = 1), weight T) ≤
        M / (lam * eps) := hmark
    _ = M * R := hdenom
    _ = C * aAct := hreplace

end YMUIC.Original24
