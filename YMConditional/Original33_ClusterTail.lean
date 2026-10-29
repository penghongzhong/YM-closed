import YMConditional.Original33_RootedCrossTail

set_option autoImplicit false
noncomputable section
namespace YMUIC.ConditionalCluster

open Filter
open scoped Topology BigOperators

variable {Cluster : Type*}

/-- From an actual rooted-polymer count, coefficient bound and the SAME
geometric length dictionary, obtain the full complex connected-cluster tail.
No clustering, mass gap, or global time-frame is assumed in this statement. -/
theorem connected_cross_polymer_decay
    {κ σ ε Cnt Cgeo Crt dist : ℝ}
    (hασ : σ < κ) (hε : 0 ≤ ε) (hCnt : 0 ≤ Cnt)
    (hCgeo : 0 < Cgeo)
    (F : ℕ → Finset Cluster) (a : Cluster → ℂ)
    (hcount : ∀ n, ((F n).card : ℝ) ≤ Cnt * Real.exp (σ * (n : ℝ)))
    (hweight : ∀ n γ, γ ∈ F n → ‖a γ‖ ≤ ε * Real.exp (-κ * (n : ℝ)))
    (hactualDistance : ∀ n γ, γ ∈ F n → dist ≤ Cgeo * (n : ℝ) + Crt) :
    Summable (crossLevel F a) ∧
      ‖∑' n : ℕ, crossLevel F a n‖ ≤
        (ε * Cnt / (1- Real.exp (-(κ-σ)))) *
          Real.exp (-((κ-σ)/Cgeo)*(dist-Crt)) := by
  classical
  let q : ℝ := Real.exp (-(κ-σ))
  have hqpos : 0 < q := Real.exp_pos _
  have hqle : 0 ≤ q := hqpos.le
  have hq : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  let N : ℕ := Nat.ceil ((dist - Crt) / Cgeo)
  have hsmall : ∀ n, ‖crossLevel F a n‖ ≤ (ε * Cnt) * q ^ n := by
    intro n
    simpa only [q] using rooted_count_to_level_bound hε F a hcount hweight n
  have hmajor : Summable (fun n : ℕ => (ε * Cnt) * q ^ n) :=
    (summable_geometric_of_lt_one hqle hq).mul_left (ε*Cnt)
  have hsum : Summable (crossLevel F a) :=
    Summable.of_norm_bounded hmajor hsmall
  have hprefix : ∀ n, n < N → F n = ∅ := by
    intro n hn
    by_contra hnon
    obtain ⟨γ,hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hnon
    have hlt : (n : ℝ) < (dist-Crt)/Cgeo :=
      (Nat.lt_ceil).mp hn
    have hbelow : Cgeo * (n:ℝ) < dist-Crt := by
      apply (lt_div_iff₀ hCgeo).mp at hlt
      nlinarith
    have hreach := hactualDistance n γ hγ
    linarith
  have hsumzero : ∑ n ∈ Finset.range N, crossLevel F a n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [crossLevel, hprefix n (Finset.mem_range.mp hn)]
  have hshift : (∑' n : ℕ, crossLevel F a n) =
      ∑' n : ℕ, crossLevel F a (n+N) := by
    have heq := hsum.sum_add_tsum_nat_add N
    rw [hsumzero, zero_add] at heq
    exact heq.symm
  have hboundShift (n : ℕ) :
      ‖crossLevel F a (n+N)‖ ≤ (ε*Cnt*q^N)*q^n := by
    have h := hsmall (n+N)
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using h
  have hmajorShift : Summable (fun n : ℕ => (ε*Cnt*q^N)*q^n) :=
    (summable_geometric_of_lt_one hqle hq).mul_left (ε*Cnt*q^N)
  have hboundSeries := tsum_of_norm_bounded hmajorShift.hasSum hboundShift
  have hN : (dist-Crt)/Cgeo ≤ (N:ℝ) := Nat.le_ceil _
  have he : q^N ≤ Real.exp (-((κ-σ)/Cgeo)*(dist-Crt)) := by
    rw [show q^N = Real.exp (-(κ-σ)*(N:ℝ)) by
      rw [show q = Real.exp (-(κ-σ)) by rfl]
      rw [← Real.exp_nat_mul]
      congr 1; ring]
    apply Real.exp_le_exp.mpr
    have halpha : 0 < κ-σ := sub_pos.mpr hασ
    have hd : (dist-Crt) / Cgeo * (κ-σ) ≤ (N:ℝ)*(κ-σ) :=
      mul_le_mul_of_nonneg_right hN halpha.le
    have heq : ((dist-Crt)/Cgeo)*(κ-σ) = ((κ-σ)/Cgeo)*(dist-Crt) := by ring
    linarith [hd, heq]
  have hdiv : 0 ≤ (ε*Cnt)/(1-q) := by
    apply div_nonneg (mul_nonneg hε hCnt)
    linarith
  refine ⟨hsum, ?_⟩
  calc
    ‖∑' n : ℕ, crossLevel F a n‖ =
      ‖∑' n : ℕ, crossLevel F a (n+N)‖ := congrArg norm hshift
    _ ≤ ∑' n : ℕ, (ε*Cnt*q^N)*q^n := hboundSeries
    _ = ((ε*Cnt)/(1-q))*q^N := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hqle hq]
      field_simp
    _ ≤ ((ε*Cnt)/(1-q))*Real.exp (-((κ-σ)/Cgeo)*(dist-Crt)) := by
      exact mul_le_mul_of_nonneg_left he hdiv
    _ = _ := by rfl

#print axioms connected_cross_polymer_decay
end YMUIC.ConditionalCluster
