import Mathlib

set_option autoImplicit false

/-!
# U2 root does not enter bulk placement entropy: distance extraction

Standalone scalar certificate for v133 equation `rootstep3`.

Let
  delta = kappa - cGeo * mu.
If
  dRoot <= cGeo * D + cRt,
then for any nonnegative bulk product B,

  exp(mu*dRoot) * B
    <= exp(mu*cRt) * B * exp(kappa*D) * exp(-delta*D).

This is the exact exponential extraction used before the rooted-tree sum.
-/

namespace YMUICV128.Section03.T007A

def delta (kappa mu : ℝ) (cGeo : ℕ) : ℝ :=
  kappa - (cGeo : ℝ) * mu

theorem damped_scalar_identity
    (bulk kappa mu D : ℝ)
    (cGeo : ℕ) :
    bulk * Real.exp (kappa * D) *
        Real.exp ((- delta kappa mu cGeo) * D)
      =
    bulk * Real.exp ((cGeo : ℝ) * mu * D) := by
  calc
    bulk * Real.exp (kappa * D) *
        Real.exp ((- delta kappa mu cGeo) * D)
        =
      bulk *
        (Real.exp (kappa * D) *
          Real.exp ((- delta kappa mu cGeo) * D)) := by ring
    _ =
      bulk *
        Real.exp
          (kappa * D + (- delta kappa mu cGeo) * D) := by
      rw [← Real.exp_add]
    _ =
      bulk * Real.exp ((cGeo : ℝ) * mu * D) := by
      congr 2
      unfold delta
      ring

theorem root_distance_weight_extraction
    {bulk kappa mu D dRoot cRt : ℝ}
    {cGeo : ℕ}
    (hbulk : 0 ≤ bulk)
    (hmu : 0 ≤ mu)
    (hDistance :
      dRoot ≤ (cGeo : ℝ) * D + cRt) :
    Real.exp (mu * dRoot) * bulk
      ≤
    Real.exp (mu * cRt) *
      (bulk * Real.exp (kappa * D) *
        Real.exp ((- delta kappa mu cGeo) * D)) := by
  have hmul :
      mu * dRoot
        ≤ mu * ((cGeo : ℝ) * D + cRt) :=
    mul_le_mul_of_nonneg_left hDistance hmu
  have hexp :
      Real.exp (mu * dRoot)
        ≤ Real.exp (mu * ((cGeo : ℝ) * D + cRt)) :=
    Real.exp_le_exp.mpr hmul
  have hweighted :
      Real.exp (mu * dRoot) * bulk
        ≤ Real.exp (mu * ((cGeo : ℝ) * D + cRt)) * bulk :=
    mul_le_mul_of_nonneg_right hexp hbulk
  calc
    Real.exp (mu * dRoot) * bulk
        ≤
      Real.exp (mu * ((cGeo : ℝ) * D + cRt)) * bulk :=
      hweighted
    _ =
      Real.exp (mu * cRt) *
        (bulk * Real.exp (kappa * D) *
          Real.exp ((- delta kappa mu cGeo) * D)) := by
      rw [damped_scalar_identity]
      have hExp :
          mu * ((cGeo : ℝ) * D + cRt)
            =
          mu * cRt + (cGeo : ℝ) * mu * D := by
        ring
      rw [hExp, Real.exp_add]
      ring

#print axioms damped_scalar_identity
#print axioms root_distance_weight_extraction

end YMUICV128.Section03.T007A
