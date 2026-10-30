import YMOriginal.Original24_FromPublishedU1ConnectedB10
import YMOriginal.Original24_NativeShellU1
import YMOriginal.Original24_PlacementRatio
import YMOriginal.Original24_PostRLocalization

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original24
open YMUIC.Wilson
open YMUICV128.Section02
open YMUICV128.Section03

/-!
# C29 Original24 §15.7: strict actual-Schwartz post-R all-scale closure

Use the SAME actual SU2 Wilson roots, SAME old/new published U1 fields,
SAME physical 4D Schwartz source and SAME p-rooted Penrose/FP tree
inputs at every scale. There is NO hypothesis on a fifth-order Taylor
remainder, post-R tail, its summability, or final source-class CLOSED.

The finite-order source Taylor remainder is derived using the *actual*
Schwartz fifth derivative and the U2 weighted exponential fifth
moment. Then ALL RG generations m are summed, with the 4-dimensional
placement entropy L^(4m) and a fixed source-norm loss L^(theta*m):
  L^((4+theta)m) * (L^(-m))^5 = L^(-(1-theta)m).
Thus any fixed 0<theta<1 gives an actual convergent geometric tail.

The exact native CMP119/122 history-to-polymer FP enumeration,
canonical a^(4-d) source jet, and the unchanged C29 Original24
terminal #24 are STILL separate physical/model obligations.
-/

/-- One physical fixed-D Schwartz source, original old/new connected
Wilson root coefficients and explicit RG block factor L produce a
FULL nonnegative absolutely summable post-R scale tail WITHOUT
postulating hB10 or the tail summability.

The only external rooted hypotheses are the same preceding
published/model U1 and Penrose/FP finite-height inputs needed for
the actual connected source coefficients. -/
theorem original24_real_connected_schwartz_postR_all_scales
    {Γ Ω T S : Type*} [Fintype Γ] [Fintype T] [Fintype S]
    (D : U1Data Γ Ω) (pub : U1PublishedHypotheses D)
    (N chi j : ℕ) (omega : Ω)
    (support : Γ → Finset (PeriodicBlock N))
    (d : Γ → ℕ)
    (hdictionary : ∀ X, D.d j X = (d X : ℝ))
    (root : Finset (PeriodicBlock N))
    (kappa mu cGeo Cpol cpol : ℝ)
    (hCpol : 0 ≤ Cpol)
    (hgap : 0 < D.kappaR - kappa - cpol)
    (hShell : ∀ Delta : PeriodicBlock N, ∀ m : ℕ,
      ((actualThroughBlock support Delta).filter
        (fun X => d X = m)).card ≤
          Cpol * Real.exp (cpol * (m : ℝ)))
    (hg : 0 < D.g j) (hgw : D.g j ≤ D.gamma)
    (hCR : 0 ≤ D.CR) (hCRnew : 0 ≤ D.CRnew)
    (hmu : 0 < mu)
    (hdelta : 0 < kappa - cGeo * mu)
    (hsize : ∀ X, (support X).card ≤ d X)
    (hweakOld :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (oldRActivityFactor (D.g j) D.kappa0 D.CR *
          (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ≤
          (kappa - cGeo * mu) / 2)
    (hweakNew :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (newRActivityFactor (D.g j) D.CRnew D.p0 *
          (Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol))))) ≤
          (kappa - cGeo * mu) / 2)
    (base : PeriodicBlock N)
    (links : PeriodicBlock N → PeriodicBlock N → SU2)
    (wp : T → List (List (ClosedLinkWalkAt (PeriodicBlock N) base)))
    (cp : T → ℂ)
    (wq : S → List (List (ClosedLinkWalkAt (PeriodicBlock N) base)))
    (cq : S → ℂ)
    (s t : ℂ) (radius Bp Bq : ℝ)
    (hr : 0 ≤ radius) (hp0 : 0 ≤ Bp) (hq0 : 0 ≤ Bq)
    (hs : ‖s‖ ≤ radius) (ht : ‖t‖ ≤ radius)
    (hp : actualWilsonPolynomialBudget wp cp ≤ Bp)
    (hq : actualWilsonPolynomialBudget wq cq ≤ Bq)
    (PhiOld PhiNew : ℕ → ℂ)
    (position displacement : ℕ → TestSpace4)
    (treeOld treeNew : ℕ → ℝ)
    (hPenroseOld : ∀ n,
      ‖PhiOld n‖ * Real.exp (mu * ‖displacement n‖) ≤ treeOld n)
    (hPenroseNew : ∀ n,
      ‖PhiNew n‖ * Real.exp (mu * ‖displacement n‖) ≤ treeNew n)
    (hFPold : ∀ n,
      (∑ k ∈ Finset.range n, treeOld k) ≤
        actualPeriodicFirstRootSum N chi root support
          (fun X => D.oldR j X omega) d cGeo mu n)
    (hFPnew : ∀ n,
      (∑ k ∈ Finset.range n, treeNew k) ≤
        actualPeriodicFirstRootSum N chi root support
          (fun X => D.newR j X omega) d cGeo mu n)
    (f : SchwartzMap TestSpace4 ℂ) (Mf : ℝ)
    (hMf : 0 ≤ Mf) (hTest : SchwartzMap.seminorm ℂ 0 5 f ≤ Mf)
    (L theta : ℝ) (hL : 1 < L)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (truncation : ℕ) :
    let Ccount : ℝ :=
      Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))
    let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
      fun w => actualWalkHolonomy links base w.vertices
    let K : ℝ := (Real.exp (radius * Bp) - 1) *
      (Real.exp (radius * Bq) - 1)
    let Croot : ℝ := ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
      (root.card : ℝ))
    let Aold : ℝ := oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount
    let Anew : ℝ := newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount
    let M : ℝ := ((5 * (K * (Croot * Aold)) / mu ^ 5) * Mf) +
      ((5 * (K * (Croot * Anew)) / mu ^ 5) * Mf)
    let q : ℝ := L ^ (-(1 - theta) : ℝ)
    let rem : ℕ → ℂ := fun m =>
      (((L ^ ((4 + theta) * (m : ℝ))) : ℝ) : ℂ) *
        (finiteMarkedTaylorRemainder
          (fun i : Fin truncation => actualTwoRootInsertion
            U wp cp wq cq s t * PhiOld i.val)
          (actualSchwartzTaylorLine f
            (fun i : Fin truncation => position i.val)
            (fun i : Fin truncation => displacement i.val)
            (L ^ (-(m : ℝ)))) +
        finiteMarkedTaylorRemainder
          (fun i : Fin truncation => actualTwoRootInsertion
            U wp cp wq cq s t * PhiNew i.val)
          (actualSchwartzTaylorLine f
            (fun i : Fin truncation => position i.val)
            (fun i : Fin truncation => displacement i.val)
            (L ^ (-(m : ℝ)))))
    (∀ m, ‖rem m‖ ≤ M * q ^ m) ∧
    Summable (fun m => ‖rem m‖) ∧
    (∑' m, ‖rem m‖) ≤ M / (1 - q) := by
  dsimp
  let Ccount : ℝ :=
    Cpol / (1 - Real.exp (-(D.kappaR - kappa - cpol)))
  have hcount : ∀ Delta : PeriodicBlock N,
      (∑ X ∈ actualThroughBlock support Delta,
        Real.exp (-(D.kappaR - kappa) * (d X : ℝ))) ≤ Ccount :=
    actual_native_U1_shell_count_to_block_norm
      support d Cpol cpol D.kappaR kappa hCpol hgap hShell
  have hden : 0 < 1 - Real.exp (-(D.kappaR - kappa - cpol)) := by
    have he : Real.exp (-(D.kappaR - kappa - cpol)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith [hgap])
    linarith
  have hCount : 0 ≤ Ccount := div_nonneg hCpol hden.le
  have hweakOld' :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount) ≤
          (kappa - cGeo * mu) / 2 := by
    simpa only [Ccount] using hweakOld
  have hweakNew' :
      (((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
        (newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount) ≤
          (kappa - cGeo * mu) / 2 := by
    simpa only [Ccount] using hweakNew
  let U : ClosedLinkWalkAt (PeriodicBlock N) base → SU2 :=
    fun w => actualWalkHolonomy links base w.vertices
  let K : ℝ := (Real.exp (radius * Bp) - 1) *
    (Real.exp (radius * Bq) - 1)
  let Croot : ℝ := ((((2 * chi + 1 : ℕ) ^ 4 : ℕ) : ℝ) *
    (root.card : ℝ))
  let Aold : ℝ := oldRActivityFactor (D.g j) D.kappa0 D.CR * Ccount
  let Anew : ℝ := newRActivityFactor (D.g j) D.CRnew D.p0 * Ccount
  let Qold : ℝ := (5 * (K * (Croot * Aold)) / mu ^ 5) * Mf
  let Qnew : ℝ := (5 * (K * (Croot * Anew)) / mu ^ 5) * Mf
  let M : ℝ := Qold + Qnew
  let q : ℝ := L ^ (-(1 - theta) : ℝ)
  let oldK : Fin truncation → ℂ :=
    fun i => actualTwoRootInsertion U wp cp wq cq s t * PhiOld i.val
  let newK : Fin truncation → ℂ :=
    fun i => actualTwoRootInsertion U wp cp wq cq s t * PhiNew i.val
  let pos : Fin truncation → TestSpace4 := fun i => position i.val
  let disp : Fin truncation → TestSpace4 := fun i => displacement i.val
  let oldRem : ℕ → ℂ := fun m =>
    finiteMarkedTaylorRemainder oldK
      (actualSchwartzTaylorLine f pos disp (L ^ (-(m : ℝ))))
  let newRem : ℕ → ℂ := fun m =>
    finiteMarkedTaylorRemainder newK
      (actualSchwartzTaylorLine f pos disp (L ^ (-(m : ℝ))))
  let rem : ℕ → ℂ := fun m =>
    (((L ^ ((4 + theta) * (m : ℝ))) : ℝ) : ℂ) *
      (oldRem m + newRem m)
  have hLpos : 0 < L := by linarith
  have hratio (m : ℕ) : 0 ≤ L ^ (-(m : ℝ)) :=
    (Real.rpow_pos_of_pos hLpos _).le
  have hTest' :
      SchwartzMap.seminorm ℂ 0 5 f ≤ Mf / (1 : ℝ) ^ 5 := by
    simpa using hTest
  have hratioId (m : ℕ) :
      L ^ ((4 + theta) * (m : ℝ)) *
        (L ^ (-(m : ℝ))) ^ 5 = q ^ m := by
    have hp5 :
        (L ^ (-(m : ℝ))) ^ (5 : ℕ) =
          L ^ (-(m : ℝ) * (5 : ℝ)) := by
      calc
        _ = (L ^ (-(m : ℝ))) ^ (5 : ℝ) :=
          (Real.rpow_natCast _ 5).symm
        _ = L ^ (-(m : ℝ) * (5 : ℝ)) := by
          rw [Real.rpow_mul hLpos.le]
    calc
      L ^ ((4 + theta) * (m : ℝ)) *
          (L ^ (-(m : ℝ))) ^ 5 =
        L ^ ((4 + theta) * (m : ℝ)) *
          L ^ (-(m : ℝ) * (5 : ℝ)) := by rw [hp5]
      _ = L ^ ((4 + theta) * (m : ℝ) + -(m : ℝ) * 5) := by
            rw [Real.rpow_add hLpos]
      _ = L ^ (-(1 - theta) * (m : ℝ)) := by
            congr 1
            ring
      _ = q ^ m := by
            dsimp [q]
            rw [Real.rpow_mul hLpos.le, Real.rpow_natCast]
  have hbound (m : ℕ) : ‖rem m‖ ≤ M * q ^ m := by
    have hActual :=
      original24_balaban_old_new_connected_B10 D pub
        N chi j omega support d hdictionary root
        kappa mu cGeo Ccount hcount
        hg hgw hCR hCRnew hCount hmu hdelta hsize
        hweakOld' hweakNew' base links wp cp wq cq s t radius Bp Bq
        hr hp0 hq0 hs ht hp hq
        PhiOld PhiNew position displacement treeOld treeNew
        hPenroseOld hPenroseNew hFPold hFPnew
        f (L ^ (-(m : ℝ))) 1 Mf
        (hratio m) (by norm_num) hMf hTest'
    obtain ⟨hOld, hNew⟩ := hActual truncation
    have hO : ‖oldRem m‖ ≤ Qold * (L ^ (-(m : ℝ))) ^ 5 := by
      simpa only [oldRem, oldK, pos, disp, Qold, K, Croot, Aold,
        div_one] using hOld
    have hN : ‖newRem m‖ ≤ Qnew * (L ^ (-(m : ℝ))) ^ 5 := by
      simpa only [newRem, newK, pos, disp, Qnew, K, Croot, Anew,
        div_one] using hNew
    have hsum :
        ‖oldRem m + newRem m‖ ≤
          M * (L ^ (-(m : ℝ))) ^ 5 := by
      calc
        _ ≤ ‖oldRem m‖ + ‖newRem m‖ :=
          norm_add_le _ _
        _ ≤ Qold * (L ^ (-(m : ℝ))) ^ 5 +
            Qnew * (L ^ (-(m : ℝ))) ^ 5 :=
          add_le_add hO hN
        _ = M * (L ^ (-(m : ℝ))) ^ 5 := by dsimp [M]; ring
    have hscale : 0 ≤ L ^ ((4 + theta) * (m : ℝ)) :=
      (Real.rpow_pos_of_pos hLpos _).le
    calc
      ‖rem m‖ =
        L ^ ((4 + theta) * (m : ℝ)) *
          ‖oldRem m + newRem m‖ := by
        simp only [rem, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hscale]
      _ ≤ L ^ ((4 + theta) * (m : ℝ)) *
          (M * (L ^ (-(m : ℝ))) ^ 5) :=
        mul_le_mul_of_nonneg_left hsum hscale
      _ = M * q ^ m := by rw [← hratioId m]; ring
  have hq :=
    original24_four_dimensional_q_contracts L theta hL htheta0 htheta1
  have hsum := finite_marked_remainder_geometric
    q M hq.1.le hq.2 rem hbound
  exact ⟨hbound, hsum.1, hsum.2⟩

end YMUIC.Original24
