import YM.Wilson.SourceDirection

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Genuine noncommutative SU(2) Wilson words

The holonomy is a genuine ordered product in SU(2), so the bound is
independent of word length.  The finite linear combination of such
Wilson words is a bounded bare source observable.

The fixed-template continuum jet expansion, normalized scaling, products
of several Wilson characters, source mixing and actual RG remainder are
not supplied by this file.
-/

/-- Noncommuting ordered holonomy along a finite SU(2) word. -/
def wilsonWordHolonomy {P : Type*} (U : P → SU2) (w : List P) : SU2 :=
  (w.map U).prod

/-- The genuine Wilson root of an ordered SU(2) word. -/
def wilsonWordRoot {P : Type*} (U : P → SU2) (w : List P) : ℝ :=
  wilsonRoot (wilsonWordHolonomy U w)

theorem wilson_word_root_bounds {P : Type*}
    (U : P → SU2) (w : List P) :
    0 ≤ wilsonWordRoot U w ∧ wilsonWordRoot U w ≤ 4 :=
  wilsonRoot_bounds (wilsonWordHolonomy U w)

theorem wilson_word_root_norm_le_four {P : Type*}
    (U : P → SU2) (w : List P) :
    ‖(wilsonWordRoot U w : ℂ)‖ ≤ 4 := by
  obtain ⟨h0, h4⟩ := wilson_word_root_bounds U w
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h4

/-- Arbitrary fixed finite complex linear combination of actual
ordered Wilson words.  Each individual word may have arbitrary
finite length, with no loss in the uniform SU(2) trace bound. -/
def wilsonWordCombination
    {P T : Type*} [Fintype T] (U : P → SU2)
    (words : T → List P) (coeff : T → ℂ) : ℂ :=
  ∑ t : T, coeff t * (wilsonWordRoot U (words t) : ℂ)

theorem wilson_word_combination_bound
    {P T : Type*} [Fintype T] (U : P → SU2)
    (words : T → List P) (coeff : T → ℂ) :
    ‖wilsonWordCombination U words coeff‖ ≤
      4 * ∑ t : T, ‖coeff t‖ := by
  calc
    ‖wilsonWordCombination U words coeff‖ ≤
        ∑ t : T, ‖coeff t * (wilsonWordRoot U (words t) : ℂ)‖ := by
          exact norm_sum_le _ _
    _ = ∑ t : T,
          ‖coeff t‖ * ‖(wilsonWordRoot U (words t) : ℂ)‖ := by
            simp only [norm_mul]
    _ ≤ ∑ t : T, ‖coeff t‖ * 4 := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left
            (wilson_word_root_norm_le_four U (words t)) (norm_nonneg _)
    _ = 4 * ∑ t : T, ‖coeff t‖ := by
          rw [← Finset.sum_mul]
          ring

/-- The genuine finite Wilson-word source evaluated against a Schwartz
test.  No abstract source functional is used. -/
def wilsonWordSchwartzSource
    {P T : Type*} [Fintype T] (U : P → SU2)
    (words : T → List P) (coeff : T → ℂ)
    (x : Space4) (f : SchwartzMap Space4 ℂ) : ℂ :=
  f x * wilsonWordCombination U words coeff

theorem wilson_word_schwartz_source_bound
    {P T : Type*} [Fintype T] (U : P → SU2)
    (words : T → List P) (coeff : T → ℂ)
    (x : Space4) (f : SchwartzMap Space4 ℂ) :
    ‖wilsonWordSchwartzSource U words coeff x f‖ ≤
      4 * (∑ t : T, ‖coeff t‖) *
        SchwartzMap.seminorm ℂ 0 0 f := by
  have hf : ‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f :=
    f.norm_le_seminorm ℂ x
  have hcomb := wilson_word_combination_bound U words coeff
  calc
    ‖wilsonWordSchwartzSource U words coeff x f‖ =
        ‖f x‖ * ‖wilsonWordCombination U words coeff‖ := by
          simp only [wilsonWordSchwartzSource, norm_mul]
    _ ≤ SchwartzMap.seminorm ℂ 0 0 f *
          (4 * ∑ t : T, ‖coeff t‖) :=
            mul_le_mul hf hcomb (norm_nonneg _) (apply_nonneg _ _)
    _ = 4 * (∑ t : T, ‖coeff t‖) *
          SchwartzMap.seminorm ℂ 0 0 f := by ring

end YMUIC.Wilson
