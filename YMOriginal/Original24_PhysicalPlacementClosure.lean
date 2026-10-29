import YMOriginal.Original24_ActualWordSourceClosure
import YMOriginal.Original24_PlacementRatio

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24: physical L, theta substitution, no arbitrary geometric q

C29 B10/Original24's actual input is 4D block placement L^(4m)
times fifth-order Taylor remainder L^(-(5-theta)m). We derive
q = L^(-(1-theta)), verify 0<q<1, and use the certified
actual SU2 finite Wilson-word old/new-R source tree bounds to
prove the resulting post-R tail is summable at every finite D.

The analytic fifth-order remainder hB10, unmarked U1/U2 native
geometry/counting inputs and actual root normalization still require
source-level correspondence to the Yang-Mills history/RG model;
none is declared as a new Lean axiom.
-/

theorem actual_word_four_dimensional_post_r_tail
    {P T Γ : Type*} [Fintype T]
    (U : P → SU2)
    (words : T → List (List P)) (coeff : T → ℂ)
    (s : ℂ)
    (hsmall : ‖s‖ * actualWilsonPolynomialBudget words coeff ≤ 1)
    (oldR newR : Γ → ℂ) (treeOld treeNew : Γ → ℝ)
    (mu cRt dRoot aOld aNew : ℝ) (Nroot : ℕ)
    (htreeOld : ∀ γ, 0 ≤ treeOld γ)
    (htreeNew : ∀ γ, 0 ≤ treeNew γ)
    (hweightedOld : ∀ γ,
      Real.exp (mu * dRoot) * ‖oldR γ‖ ≤
        Real.exp (mu * cRt) * treeOld γ)
    (hweightedNew : ∀ γ,
      Real.exp (mu * dRoot) * ‖newR γ‖ ≤
        Real.exp (mu * cRt) * treeNew γ)
    (hsumOld : Summable treeOld) (hsumNew : Summable treeNew)
    (hboundOld : (∑' γ, treeOld γ) ≤ (Nroot : ℝ) * aOld)
    (hboundNew : (∑' γ, treeNew γ) ≤ (Nroot : ℝ) * aNew)
    (L theta : ℝ) (hL : 1 < L)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (remainder : ℕ → ℂ)
    (hB10 : ∀ m, ‖remainder m‖ ≤
      ((∑' γ, ‖actualWordMarkedR U words coeff s oldR γ‖) +
        (∑' γ, ‖actualWordMarkedR U words coeff s newR γ‖)) *
      (L ^ (4 * m) * L ^ (-(5 - theta) * (m : ℝ)))) :
    Summable (fun m => ‖remainder m‖) ∧
      (∑' m, ‖remainder m‖) ≤
        ((2 * ‖s‖ * actualWilsonPolynomialBudget words coeff) *
          Real.exp (mu * cRt) * (Nroot : ℝ) *
          (aOld + aNew) * Real.exp (-mu * dRoot)) /
          (1 - L ^ (-(1 - theta) : ℝ)) := by
  obtain ⟨hq0, hq1⟩ :=
    original24_four_dimensional_q_contracts L theta hL htheta0 htheta1
  have hB10q (m : ℕ) :
      ‖remainder m‖ ≤
        ((∑' γ, ‖actualWordMarkedR U words coeff s oldR γ‖) +
          (∑' γ, ‖actualWordMarkedR U words coeff s newR γ‖)) *
          (L ^ (-(1 - theta) : ℝ)) ^ m := by
    simpa only [original24_four_dimensional_power_identity L theta hL m] using
      hB10 m
  exact actual_word_post_r_localization_summable
    U words coeff s hsmall oldR newR treeOld treeNew
    mu cRt dRoot aOld aNew Nroot htreeOld htreeNew
    hweightedOld hweightedNew hsumOld hsumNew hboundOld hboundNew
    (L ^ (-(1 - theta) : ℝ)) hq0.le hq1 remainder hB10q

end YMUIC.Original24
