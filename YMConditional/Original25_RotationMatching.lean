import YMConditional.Original25_TwoScaleLimit
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace YMUIC.RotationMatching

abbrev Space4 := EuclideanSpace ℝ (Fin 4)
abbrev Rotation4 := Space4 ≃ₗᵢ[ℝ] Space4

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The actual tensor-field pullback: rho(R) f(R^{-1} x).
No rotation on a fixed hypercubic regulator is introduced. -/
def rotateField (R : Rotation4) (rho : V →ₗ[ℂ] V) (f : Space4 → V) : Space4 → V :=
  fun x => rho (f (R.symm x))

def rotateFamily {n : ℕ} (R : Rotation4) (rho : V →ₗ[ℂ] V)
    (f : Fin n → Space4 → V) : Fin n → Space4 → V :=
  fun j => rotateField R rho (f j)

/-- Check the inverse spatial pullback and tensor-composition orders. -/
theorem rotateField_composition
    (R S : Rotation4) (rhoR rhoS : V →ₗ[ℂ] V) (f : Space4 → V) :
    rotateField R rhoR (rotateField S rhoS f) =
      rotateField (S.trans R) (rhoR.comp rhoS) f := by
  rfl

/-- Original25 / C29 Theorem16.1, equation328. The same finite family is read
in a standard regulator and its rotated regulator. The relabeling identity
is ONLY between those two regulators, not an assumed symmetry of one lattice.

All original prior inputs are visible: exact regulator/source identification,
fixed-history old and recent estimates, one-sided running-coupling modulus,
and the two values of the SAME joint continuum functional. The old constant
is independent of the history cut; the recent constants need not be.
The theorem does NOT construct the Wilson estimates (326)-(327) or the joint
limits. No I7, no continuum rotation identity and no new axiom is assumed. -/
theorem original25_continuous_rotation_matching
    {ι : Type*} {l : Filter ι} [l.NeBot] {n : ℕ}
    (R : Rotation4) (rho : V →ₗ[ℂ] V) (f : Fin n → Space4 → V)
    (standard rotated : ι → (Fin n → Space4 → V) → ℂ)
    (S : (Fin n → Space4 → V) → ℂ)
    (hstandard : Tendsto (fun i => standard i f) l (𝓝 (S f)))
    (htransformed : Tendsto (fun i => standard i (rotateFamily R rho f)) l
      (𝓝 (S (rotateFamily R rho f))))
    (hrelabel : ∀ᶠ i in l, rotated i f = standard i (rotateFamily R rho f))
    {L theta : ℝ} (hL : 1 < L) (htheta : theta < 1)
    (a g : ι → ℝ) (epsilon : ℝ → ℝ)
    (ha : Tendsto a l (𝓝 0)) (hg : Tendsto g l (𝓝 0))
    (hgpos : ∀ᶠ i in l, 0 < g i)
    (hepsilon : Tendsto epsilon (𝓝[>] (0 : ℝ)) (𝓝 0))
    (old recent : ℕ → ι → ℂ) (C : ℝ) (C_recent : ℕ → ℝ)
    (hsplit : ∀ N, ∀ᶠ i in l, rotated i f - standard i f = old N i + recent N i)
    (hold : ∀ N, ∀ᶠ i in l, ‖old N i‖ ≤ C *
      ∑' k : ℕ, L ^ (4 * ((N+k : ℕ) : ℝ)) *
        L ^ (-(5-theta) * ((N+k : ℕ) : ℝ)))
    (hrecent : ∀ N, ∀ᶠ i in l,
      ‖recent N i‖ ≤ C_recent N * ((a i)^2 + epsilon (g i))) :
    S (rotateFamily R rho f) = S f := by
  have hrotated : Tendsto (fun i => rotated i f) l
      (𝓝 (S (rotateFamily R rho f))) := htransformed.congr' (hrelabel.mono (fun _ h => h.symm))
  obtain ⟨hq0, hq1⟩ := historyRatio_bounds hL htheta
  have hold' : ∀ N, ∀ᶠ i in l,
      ‖old N i‖ ≤ C * historyRatio L theta ^ N / (1-historyRatio L theta) := by
    intro N
    filter_upwards [hold N] with i hi
    rw [(old_history_series hL htheta N).tsum_eq] at hi
    simpa only [mul_div_assoc] using hi
  exact equal_limits_of_old_recent hq0.le hq1 hrotated hstandard
    old recent C_recent (fun i => (a i)^2 + epsilon (g i))
    (recent_error_tendsto a g epsilon ha hg hgpos hepsilon)
    hsplit hold' hrecent

/-- Exact original tail-form (326): same conclusion when the preceding
old-history summation has already been performed. No uniform recent bound
in N is added. This entry displays the original paper's numerical bound. -/
theorem original25_from_summed_history_bounds
    {ι : Type*} {l : Filter ι} [l.NeBot] {n : ℕ}
    (R : Rotation4) (rho : V →ₗ[ℂ] V) (f : Fin n → Space4 → V)
    (standard rotated : ι → (Fin n → Space4 → V) → ℂ)
    (S : (Fin n → Space4 → V) → ℂ)
    (hstandard : Tendsto (fun i => standard i f) l (𝓝 (S f)))
    (htransformed : Tendsto (fun i => standard i (rotateFamily R rho f)) l
      (𝓝 (S (rotateFamily R rho f))))
    (hrelabel : ∀ᶠ i in l, rotated i f = standard i (rotateFamily R rho f))
    {L theta : ℝ} (hL : 1 < L) (htheta : theta < 1)
    (a g : ι → ℝ) (epsilon : ℝ → ℝ)
    (ha : Tendsto a l (𝓝 0)) (hg : Tendsto g l (𝓝 0))
    (hgpos : ∀ᶠ i in l, 0 < g i)
    (hepsilon : Tendsto epsilon (𝓝[>] (0 : ℝ)) (𝓝 0))
    (old recent : ℕ → ι → ℂ) (C : ℝ) (C_recent : ℕ → ℝ)
    (hsplit : ∀ N, ∀ᶠ i in l, rotated i f - standard i f = old N i + recent N i)
    (hold : ∀ N : ℕ, ∀ᶠ i in l,
      ‖old N i‖ ≤ C * L ^ (-(1-theta) * (N : ℝ)) / (1-L ^ (-(1-theta))))
    (hrecent : ∀ N, ∀ᶠ i in l,
      ‖recent N i‖ ≤ C_recent N * ((a i)^2 + epsilon (g i))) :
    S (rotateFamily R rho f) = S f := by
  apply original25_continuous_rotation_matching R rho f standard rotated S
    hstandard htransformed hrelabel hL htheta a g epsilon ha hg hgpos hepsilon
    old recent C C_recent hsplit _ hrecent
  intro N
  filter_upwards [hold N] with i hi
  rw [(old_history_series hL htheta N).tsum_eq]
  simpa only [historyRatio, Real.rpow_mul (le_of_lt (lt_trans (by norm_num) hL)),
    Real.rpow_natCast, mul_div_assoc] using hi

end YMUIC.RotationMatching
