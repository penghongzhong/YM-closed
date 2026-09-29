import Mathlib

set_option autoImplicit false

/-!
# U2 source analyticity: finite-cluster entire factors

For fixed coefficient C and fixed real plaquette values Wp,Wq, the cluster
summand
  C * (exp(s Wp)-1) * (exp(t Wq)-1)
is entire on C x C. Finite sums are entire and vanish on either coordinate
axis. This is the finite-cutoff algebraic part of lem:U2-source-analyticity.
-/

namespace YMUICV128.Section03.T008A

noncomputable def rootFactor (W : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (W : ℂ)) - 1

noncomputable def clusterPhi
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) : ℂ :=
  C * rootFactor Wp z.1 * rootFactor Wq z.2

theorem clusterPhi_analyticAt
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (clusterPhi C Wp Wq) z := by
  have hs :
      AnalyticAt ℂ (fun w : ℂ × ℂ => w.1 * (Wp : ℂ)) z :=
    analyticAt_fst.mul analyticAt_const
  have ht :
      AnalyticAt ℂ (fun w : ℂ × ℂ => w.2 * (Wq : ℂ)) z :=
    analyticAt_snd.mul analyticAt_const
  have ha :
      AnalyticAt ℂ
        (fun w : ℂ × ℂ => Complex.exp (w.1 * (Wp : ℂ)) - 1) z :=
    hs.cexp'.sub analyticAt_const
  have hb :
      AnalyticAt ℂ
        (fun w : ℂ × ℂ => Complex.exp (w.2 * (Wq : ℂ)) - 1) z :=
    ht.cexp'.sub analyticAt_const
  change AnalyticAt ℂ
    (fun w : ℂ × ℂ =>
      C * (Complex.exp (w.1 * (Wp : ℂ)) - 1) *
        (Complex.exp (w.2 * (Wq : ℂ)) - 1)) z
  exact (analyticAt_const.mul ha).mul hb

theorem clusterPhi_differentiableAt
    (C : ℂ) (Wp Wq : ℝ) (z : ℂ × ℂ) :
    DifferentiableAt ℂ (clusterPhi C Wp Wq) z :=
  (clusterPhi_analyticAt C Wp Wq z).differentiableAt

theorem clusterPhi_zero_left
    (C : ℂ) (Wp Wq : ℝ) (t : ℂ) :
    clusterPhi C Wp Wq (0,t) = 0 := by
  simp [clusterPhi, rootFactor]

theorem clusterPhi_zero_right
    (C : ℂ) (Wp Wq : ℝ) (s : ℂ) :
    clusterPhi C Wp Wq (s,0) = 0 := by
  simp [clusterPhi, rootFactor]

theorem finite_cluster_sum_analyticAt
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι)
    (C : ι → ℂ) (Wp Wq : ℝ)
    (z : ℂ × ℂ) :
    AnalyticAt ℂ
      (fun w => ∑ i ∈ S, clusterPhi (C i) Wp Wq w) z := by
  classical
  induction S using Finset.induction with
  | empty =>
      simpa using
        (analyticAt_const :
          AnalyticAt ℂ (fun _ : ℂ × ℂ => (0 : ℂ)) z)
  | @insert a S ha ih =>
      have hsum :
          (fun w => ∑ i ∈ insert a S, clusterPhi (C i) Wp Wq w)
            =
          (fun w =>
            clusterPhi (C a) Wp Wq w +
              ∑ i ∈ S, clusterPhi (C i) Wp Wq w) := by
        funext w
        simp [Finset.sum_insert ha]
      rw [hsum]
      exact (clusterPhi_analyticAt (C a) Wp Wq z).add ih

theorem finite_cluster_sum_zero_left
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι)
    (C : ι → ℂ) (Wp Wq : ℝ)
    (t : ℂ) :
    (∑ i ∈ S, clusterPhi (C i) Wp Wq (0,t)) = 0 := by
  simp [clusterPhi_zero_left]

theorem finite_cluster_sum_zero_right
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι)
    (C : ι → ℂ) (Wp Wq : ℝ)
    (s : ℂ) :
    (∑ i ∈ S, clusterPhi (C i) Wp Wq (s,0)) = 0 := by
  simp [clusterPhi_zero_right]

#print axioms clusterPhi_analyticAt
#print axioms finite_cluster_sum_analyticAt
#print axioms finite_cluster_sum_zero_left
#print axioms finite_cluster_sum_zero_right

end YMUICV128.Section03.T008A
