import YM.OSGrowth.Polymer

namespace YMUIC.OSGrowth

/-- A rooted cover converts a per-root level bound into a bound linear in the
number of source roots. No disjointness or choice of a unique root is required. -/
theorem polymer_level_count_of_root_cover
    {P V : Type*} [DecidableEq P]
    (s : Finset P) (K : Finset V) (τ : P → ℕ) (rooted : V → ℕ → Finset P)
    {B σ : ℝ}
    (hcover : ∀ X ∈ s, ∃ x ∈ K, X ∈ rooted x (τ X))
    (hrootcount : ∀ x ∈ K, ∀ n, ((rooted x n).card : ℝ) ≤ B * Real.exp (σ * n))
    (n : ℕ) :
    ((s.filter (fun X => τ X = n)).card : ℝ) ≤
      (K.card : ℝ) * B * Real.exp (σ * n) := by
  classical
  have hsub : s.filter (fun X => τ X = n) ⊆ K.biUnion (fun x => rooted x n) := by
    intro X hX
    obtain ⟨hXs, hn⟩ := Finset.mem_filter.mp hX
    obtain ⟨x, hx, hroot⟩ := hcover X hXs
    exact Finset.mem_biUnion.mpr ⟨x, hx, hn ▸ hroot⟩
  calc
    _ ≤ ((K.biUnion (fun x => rooted x n)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ((∑ x ∈ K, (rooted x n).card : ℕ) : ℝ) :=
      Nat.cast_le.mpr Finset.card_biUnion_le
    _ = ∑ x ∈ K, ((rooted x n).card : ℝ) := by simp
    _ ≤ ∑ x ∈ K, B * Real.exp (σ * n) :=
      Finset.sum_le_sum (fun x hx => hrootcount x hx n)
    _ = (K.card : ℝ) * B * Real.exp (σ * n) := by simp [mul_assoc]

end YMUIC.OSGrowth
