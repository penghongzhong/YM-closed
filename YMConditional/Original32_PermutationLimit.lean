import YMConditional.Original32_AnalyticSymmetry

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace YMUIC.SchwingerSymmetry

/-- Original #32, paper Lemma17.7 / equation351. The original finite-cutoff
analyticity and SAME-net Schwinger convergence are explicit upstream inputs.
Neither cutoff nor continuum permutation symmetry is an input.

The source spaces may vary with cutoff and volume. Test is an arbitrary
class of the original smeared source insertions; it need not be a Banach
space. Each insertion is lifted into the corresponding cutoff source space.
The continuum limits must be taken along a nontrivial filter. -/
theorem original32_permutation_symmetry
    {ι Test : Type*} {l : Filter ι} [l.NeBot]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    (Z : (i : ι) → E i → ℂ)
    (liftSource : (i : ι) → Test → E i)
    (hanalytic : ∀ᶠ i in l, AnalyticAt ℂ (Z i) 0)
    (S : (n : ℕ) → (Fin n → Test) → ℂ)
    (hjoint : ∀ n (f : Fin n → Test),
      Tendsto (fun i => cutoffSchwinger (Z i) (liftSource i) n f)
        l (𝓝 (S n f))) :
    ∀ n (f : Fin n → Test) (σ : Equiv.Perm (Fin n)),
      S n (f ∘ σ) = S n f := by
  intro n f σ
  have heq :
      (fun i => cutoffSchwinger (Z i) (liftSource i) n (f ∘ σ)) =ᶠ[l]
        (fun i => cutoffSchwinger (Z i) (liftSource i) n f) := by
    filter_upwards [hanalytic] with i hi
    exact cutoff_schwinger_permutation (Z i) hi (liftSource i) n f σ
  exact tendsto_nhds_unique ((hjoint n (f ∘ σ)).congr' heq) (hjoint n f)

/-- The actual cutoff-volume directed product net. No arbitrary subsequence
or unidentified pair of limit filters replaces the original joint limit. -/
theorem original32_cutoff_volume_net
    {Test : Type*}
    {E : (ℕ × ℕ) → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    (Z : (i : ℕ × ℕ) → E i → ℂ)
    (liftSource : (i : ℕ × ℕ) → Test → E i)
    (hanalytic : ∀ i, AnalyticAt ℂ (Z i) 0)
    (S : (n : ℕ) → (Fin n → Test) → ℂ)
    (hjoint : ∀ n (f : Fin n → Test),
      Tendsto (fun i => cutoffSchwinger (Z i) (liftSource i) n f)
        atTop (𝓝 (S n f))) :
    ∀ n (f : Fin n → Test) (σ : Equiv.Perm (Fin n)),
      S n (f ∘ σ) = S n f := by
  exact original32_permutation_symmetry Z liftSource
    (Filter.Eventually.of_forall hanalytic) S hjoint

#print axioms original32_permutation_symmetry
#print axioms original32_cutoff_volume_net

end YMUIC.SchwingerSymmetry
