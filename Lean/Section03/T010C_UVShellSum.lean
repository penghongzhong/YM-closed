import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section03.T010C

theorem uv_shell_sum_bound
    {K : ℕ}
    (cov : ℕ → ℝ)
    (Cstar mu Binf L R : ℝ)
    (hCstar : 0 ≤ Cstar)
    (hmu : 0 < mu)
    (hL : 2 ≤ L)
    (hR : 0 < R)
    (hcov :
      ∀ j < K,
        cov j ≤
          Cstar * Real.exp (mu * Binf) *
            Real.exp (-mu * L^(K-j) * R))
    (hsuper :
      ∑ n in Finset.Icc 1 K, Real.exp (-mu * L^n * R)
        ≤
      Real.exp (-mu*L*R) /
        (1 - Real.exp (-mu*L*R))) :
    ∑ j in Finset.range K, cov j
      ≤
    Cstar * Real.exp (mu * Binf) *
      (Real.exp (-mu*L*R) /
        (1 - Real.exp (-mu*L*R))) := by
  have hfac :
      0 ≤ Cstar * Real.exp (mu * Binf) := by
    positivity
  have hsum :
      ∑ j in Finset.range K, cov j
        ≤
      ∑ j in Finset.range K,
        Cstar * Real.exp (mu * Binf) *
          Real.exp (-mu * L^(K-j) * R) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hcov j (Finset.mem_range.mp hj)
  have hreindex :
      ∑ j in Finset.range K,
        Real.exp (-mu * L^(K-j) * R)
      =
      ∑ n in Finset.Icc 1 K,
        Real.exp (-mu * L^n * R) := by
    classical
    let e : Fin K ≃ {n // n ∈ Finset.Icc 1 K} :=
    { toFun := fun j =>
        ⟨K - j + 0, by
          simp only [Finset.mem_Icc]
          constructor
          · omega
          · omega⟩
      invFun := fun n =>
        ⟨K - n.1, by
          have hn := (Finset.mem_Icc.mp n.2).1
          omega⟩
      left_inv := by
        intro j
        apply Fin.ext
        simp
        omega
      right_inv := by
        intro n
        apply Subtype.ext
        simp
        have hn := Finset.mem_Icc.mp n.2
        omega }
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_subtype]
    refine Fintype.sum_equiv e ?_ ?_ ?_
    intro j
    simp [e]
  calc
    ∑ j in Finset.range K, cov j
        ≤
      ∑ j in Finset.range K,
        Cstar * Real.exp (mu * Binf) *
          Real.exp (-mu * L^(K-j) * R) := hsum
    _ =
      Cstar * Real.exp (mu * Binf) *
        ∑ j in Finset.range K,
          Real.exp (-mu * L^(K-j) * R) := by
      rw [Finset.mul_sum]
    _ =
      Cstar * Real.exp (mu * Binf) *
        ∑ n in Finset.Icc 1 K,
          Real.exp (-mu * L^n * R) := by
      rw [hreindex]
    _ ≤
      Cstar * Real.exp (mu * Binf) *
        (Real.exp (-mu*L*R) /
          (1 - Real.exp (-mu*L*R))) :=
      mul_le_mul_of_nonneg_left hsuper hfac

#print axioms uv_shell_sum_bound

end YMUICV128.Section03.T010C
