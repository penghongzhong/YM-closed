import YM.Wilson.RootBound

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30.SourceObstruction
open YMUICV128.Section03

def centralMinusOne : SU2 := ⟨-(1 : Matrix (Fin 2) (Fin 2) ℂ), by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    simp
  · rw [Matrix.det_fin_two]
    norm_num [Matrix.one_apply]
⟩

theorem root_at_centralMinusOne : wilsonRoot centralMinusOne = 4 := by
  norm_num [wilsonRoot, centralMinusOne]

/-- The unrenormalized pointwise Wilson control cannot remain uniform
    under multiplication by a^(-4), even for a single plaquette. -/
theorem no_uniform_scaled_root_bound :
    ¬ ∃ K : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∀ U : SU2, a⁻¹ ^ 4 * wilsonRoot U ≤ K := by
  intro h
  obtain ⟨K, hK⟩ := h
  let a : ℝ := 1 / (|K| + 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; have h : 0 ≤ |K| := abs_nonneg K; exact (div_le_one (by positivity)).2 (by linarith)
  have hb := hK a ha ha1 centralMinusOne
  rw [root_at_centralMinusOne] at hb
  dsimp [a] at hb
  have hp : 0 ≤ |K| := abs_nonneg K
  have hKa : K ≤ |K| := le_abs_self K
  have hid : (1 / (|K| + 2))⁻¹ = |K| + 2 := by simp
  rw [hid] at hb
  nlinarith [sq_nonneg (|K| + 2), sq_nonneg ((|K| + 2)^2 - 1)]

#print axioms root_at_centralMinusOne
#print axioms no_uniform_scaled_root_bound
end YMUIC.Original30.SourceObstruction
