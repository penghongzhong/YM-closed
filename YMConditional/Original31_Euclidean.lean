import YMConditional.Original31_Translation

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace YMUIC.EuclideanCovariance
open YMUIC.RotationMatching
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Original #31 (C29 Lemma 17.6): E1 Euclidean covariance, at each fixed
finite order, under exactly the original rotation-matching inputs of #25,
plus actual regulator-lattice translation relabeling and the corresponding
same joint smearing limit. No arbitrary continuous rotation on a fixed lattice
is hypothesized. Neither rotation nor translation covariance is an input. -/
theorem original31_euclidean_covariance
    {ι : Type*} {l : Filter ι} [l.NeBot] {n : ℕ}
    (a : Space4) (t : ι → Space4)
    (R : Rotation4) (rho : V →ₗ[ℂ] V)
    (f : Fin n → Space4 → V)
    (standard rotated : ι → (Fin n → Space4 → V) → ℂ)
    (S : (Fin n → Space4 → V) → ℂ)
    (hstandard : Tendsto (fun i => standard i f) l (𝓝 (S f)))
    (hrotated : Tendsto (fun i => standard i (rotateFamily R rho f))
      l (𝓝 (S (rotateFamily R rho f))))
    (hrelabel : ∀ᶠ i in l, rotated i f = standard i (rotateFamily R rho f))
    {L theta : ℝ} (hL : 1 < L) (htheta : theta < 1)
    (mesh g : ι → ℝ) (epsilon : ℝ → ℝ)
    (hmesh : Tendsto mesh l (𝓝 0)) (hg : Tendsto g l (𝓝 0))
    (hgpos : ∀ᶠ i in l, 0 < g i)
    (hepsilon : Tendsto epsilon (𝓝[>] (0 : ℝ)) (𝓝 0))
    (old recent : ℕ → ι → ℂ) (C : ℝ) (C_recent : ℕ → ℝ)
    (hsplit : ∀ N, ∀ᶠ i in l, rotated i f - standard i f = old N i + recent N i)
    (hold : ∀ N, ∀ᶠ i in l, ‖old N i‖ ≤ C *
      ∑' k : ℕ, L ^ (4 * ((N+k : ℕ) : ℝ)) *
        L ^ (-(5-theta) * ((N+k : ℕ) : ℝ)))
    (hrecent : ∀ N, ∀ᶠ i in l,
      ‖recent N i‖ ≤ C_recent N * ((mesh i)^2 + epsilon (g i)))
    (htranslate : ∀ᶠ i in l,
      standard i (translateFamily (t i) (rotateFamily R rho f)) =
      standard i (rotateFamily R rho f))
    (htranslateJoint : Tendsto
      (fun i => standard i (translateFamily a (rotateFamily R rho f)))
      l (𝓝 (S (euclideanFamily a R rho f))))
    (hsourceError : Tendsto
      (fun i => standard i (translateFamily (t i) (rotateFamily R rho f)) -
        standard i (translateFamily a (rotateFamily R rho f)))
      l (𝓝 (0 : ℂ))) :
    S (euclideanFamily a R rho f) = S f := by
  have hr : S (rotateFamily R rho f) = S f :=
    original25_continuous_rotation_matching R rho f standard rotated S
      hstandard hrotated hrelabel hL htheta mesh g epsilon
      hmesh hg hgpos hepsilon old recent C C_recent hsplit hold hrecent
  have ht : S (translateFamily a (rotateFamily R rho f)) =
      S (rotateFamily R rho f) :=
    translated_limit_from_lattice_relabel a t (rotateFamily R rho f)
      standard S htranslate hrotated (by
        simpa only [euclideanFamily_eq_translation_rotation] using htranslateJoint)
      hsourceError
  simpa only [euclideanFamily_eq_translation_rotation] using ht.trans hr

#print axioms original31_euclidean_covariance
end YMUIC.EuclideanCovariance
