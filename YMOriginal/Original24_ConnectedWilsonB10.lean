import YMOriginal.Original24_ConnectedUrsellFP
import YMOriginal.Original24_ActualSchwartzB10

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section03

/-!
# Original24: actual B10 fifth-order localization of the connected
# two-root Wilson source, derived from weighted Penrose/FP + U1

Unlike previous helper assertions, the fifth-order kernel/moment bound
is NOT a hypothesis.  The exact finite Taylor remainder is computed
with the actual Schwartz test f, true source displacement, genuine
bounded SU2 Wilson double root and connected cluster coefficient Phi.

The external analytic inputs are only:
- unmarked per-block physical U1 norm and KP weak-source condition;
- the weighted pointwise hard-core Penrose comparison and the
  labeled-tree finite-height Fernández--Procacci enumeration,
  for the SAME connected history and displacement.

The physical old/new RG-history indexing and fixed-D counterterm/jet
identification must still instantiate those external interfaces.
-/

/-- Uniform finite-cutoff fifth-order B10 bound for every truncation
of the genuine double SU2 Wilson external-root connected Ursell sum.
NO hB10, hmoment, source-deformed R analyticity or full-series
summability is passed as a premise. -/
theorem original24_connected_Wilson_B10_from_U1_FP
    {P T S Γ : Type*} [Fintype T] [Fintype S] [Fintype Γ]
    (N chi : ℕ)
    (root : Finset (PeriodicBlock N))
    (support : Γ → Finset (PeriodicBlock N))
    (z : Γ → ℂ) (d : Γ → ℕ)
    (kappa mu cGeo aAct : ℝ)
    (ha : 0 ≤ aAct)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hsmall : (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * aAct ≤
      (kappa - cGeo * mu) / 2)
    (hLocalNorm : ∀ Delta : PeriodicBlock N,
      (∑ Y ∈ actualThroughBlock support Delta,
        ‖z Y‖ * Real.exp (kappa * (d Y : ℝ))) ≤ aAct)
    (U : P → SU2)
    (wp : T → List (List P)) (cp : T → ℂ)
    (wq : S → List (List P)) (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (Phi : ℕ → ℂ)
    (position displacement : ℕ → TestSpace4)
    (labeledTree : ℕ → ℝ)
    (hmu : 0 < mu)
    (hPenroseDistance : ∀ n,
      ‖Phi n‖ * Real.exp (mu * ‖displacement n‖) ≤ labeledTree n)
    (hFP : ∀ n,
      (∑ k ∈ Finset.range n, labeledTree k) ≤
        actualPeriodicFirstRootSum N chi root support z d cGeo mu n)
    (f : SchwartzMap TestSpace4 ℂ)
    (aJ aN Mf : ℝ)
    (haJ : 0 ≤ aJ) (haN : 0 < aN) (hMf : 0 ≤ Mf)
    (hTest : SchwartzMap.seminorm ℂ 0 5 f ≤ Mf / aN ^ 5) :
    let K : ℝ := (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
    let M : ℝ := K *
      (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) * (root.card : ℝ)) * aAct)
    ∀ m : ℕ,
      ‖finiteMarkedTaylorRemainder
        (fun i : Fin m =>
          actualTwoRootInsertion U wp cp wq cq s t * Phi i.val)
        (actualSchwartzTaylorLine f
          (fun i : Fin m => position i.val)
          (fun i : Fin m => displacement i.val) aJ)‖ ≤
      (5 * M / mu ^ 5) * Mf * (aJ / aN) ^ 5 := by
  dsimp
  let D : ℂ := actualTwoRootInsertion U wp cp wq cq s t
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  let Croot : ℝ :=
    (((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (root.card : ℝ)) * aAct)
  let M : ℝ := K * Croot
  have hKp : 0 ≤ Real.exp (radius * Bp) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hp0))
  have hKq : 0 ≤ Real.exp (radius * Bq) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hr hq0))
  have hK : 0 ≤ K := mul_nonneg hKp hKq
  have hD : ‖D‖ ≤ K :=
    actual_two_root_insertion_full_radius U wp cp wq cq
      s t radius Bp Bq hr hp0 hq0 hs ht hp hq
  have hroot : ∀ m,
      actualPeriodicFirstRootSum N chi root support z d cGeo mu m ≤ Croot :=
    actual_periodic_first_root_uniform N chi root support z d
      kappa mu cGeo aAct ha hdelta hsize hsmall hLocalNorm
  have hprefix (m : ℕ) :
      (∑ n ∈ Finset.range m,
        ‖Phi n‖ * Real.exp (mu * ‖displacement n‖)) ≤ Croot := by
    calc
      _ ≤ ∑ n ∈ Finset.range m, labeledTree n :=
        Finset.sum_le_sum (fun n hn => hPenroseDistance n)
      _ ≤ actualPeriodicFirstRootSum
        N chi root support z d cGeo mu m := hFP m
      _ ≤ Croot := hroot m
  have hweighted (m : ℕ) :
      (∑ n ∈ Finset.range m,
        ‖D * Phi n‖ * Real.exp (mu * ‖displacement n‖)) ≤ M := by
    calc
      _ ≤ ∑ n ∈ Finset.range m,
        K * (‖Phi n‖ * Real.exp (mu * ‖displacement n‖)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hpart : 0 ≤
            ‖Phi n‖ * Real.exp (mu * ‖displacement n‖) := by positivity
        calc
          ‖D * Phi n‖ * Real.exp (mu * ‖displacement n‖) =
              ‖D‖ * (‖Phi n‖ * Real.exp (mu * ‖displacement n‖)) := by
                simp only [norm_mul]
                ring
          _ ≤ K * (‖Phi n‖ * Real.exp (mu * ‖displacement n‖)) :=
            mul_le_mul_of_nonneg_right hD hpart
      _ = K * (∑ n ∈ Finset.range m,
        ‖Phi n‖ * Real.exp (mu * ‖displacement n‖)) := by
          rw [Finset.mul_sum]
      _ ≤ K * Croot := mul_le_mul_of_nonneg_left (hprefix m) hK
      _ = M := rfl
  intro m
  let Kmark : Fin m → ℂ := fun i => D * Phi i.val
  let pos : Fin m → TestSpace4 := fun i => position i.val
  let displ : Fin m → TestSpace4 := fun i => displacement i.val
  let length : Fin m → ℝ := fun i => ‖displ i‖
  let line : Fin m → ℝ → ℂ := actualSchwartzTaylorLine f pos displ aJ
  have hFinite :
      (∑ i : Fin m, ‖Kmark i‖ * Real.exp (mu * length i)) ≤ M := by
    simpa only [Kmark, length, displ, ← Fin.sum_univ_eq_sum_range]
      using hweighted m
  have h5 :=
    fifth_moment_from_U2_exponential Kmark length
      mu M hmu (fun i => norm_nonneg _) hFinite
  have hSmooth : ∀ i : Fin m, ContDiffOn ℝ 5 (line i) (Set.Icc 0 1) := by
    intro i
    exact (physical_test_line_smooth f (pos i)
      (aJ • displ i)).contDiffOn
  have hderiv :
      ∀ (i : Fin m) (t : ℝ), t ∈ Set.Icc 0 1 →
        ‖iteratedDerivWithin 5 (line i) (Set.Icc 0 1) t‖ ≤
          Mf * (aJ / aN) ^ 5 * (length i) ^ 5 := by
    exact actual_schwartz_directional_fifth_bound
      f pos displ aJ aN Mf haJ haN hTest
  have hTaylor := finite_marked_taylor_from_fifth_moment
      Kmark line length aJ aN Mf
      ((120 / mu ^ 5) * M)
      haJ haN hMf (fun i => norm_nonneg _) hSmooth hderiv h5
  change ‖finiteMarkedTaylorRemainder Kmark line‖ ≤
    (5 * M / mu ^ 5) * Mf * (aJ / aN) ^ 5
  calc
    _ ≤ ((120 / mu ^ 5) * M) * Mf * (aJ / aN) ^ 5 / 24 :=
      hTaylor
    _ = (5 * M / mu ^ 5) * Mf * (aJ / aN) ^ 5 := by ring

end YMUIC.Original24
