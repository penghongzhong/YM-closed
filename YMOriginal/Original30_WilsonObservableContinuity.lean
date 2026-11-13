import YMOriginal.Original24_WilsonWordPolynomial

set_option autoImplicit false

namespace YMUIC.Original30
open YMUIC.Original24 YMUIC.Wilson YMUICV128.Section03

/-- Continuity of the actual ordered SU(2) Wilson polynomial is derived
from continuity of link coordinates, including arbitrary word lengths. -/
theorem actual_wilson_polynomial_continuous
    {Ω W T : Type*} [TopologicalSpace Ω] [Fintype T]
    (U : Ω → W → SU2) (hU : ∀ w, Continuous (fun ω => U ω w))
    (words : T → List (List W)) (coeff : T → ℂ) :
    Continuous (fun ω => actualWilsonPolynomial (U ω) words coeff) := by
  have hhol (w : List W) : Continuous (fun ω => wilsonWordHolonomy (U ω) w) := by
    induction w with
    | nil => exact continuous_const
    | cons w rest ih => exact (hU w).mul ih
  have hroot : Continuous (fun V : SU2 => (wilsonRoot V : ℂ)) := by
    unfold wilsonRoot
    fun_prop
  have hmono (ws : List (List W)) :
      Continuous (fun ω => actualWilsonMonomial (U ω) ws) := by
    induction ws with
    | nil => exact continuous_const
    | cons w rest ih => exact (hroot.comp (hhol w)).mul ih
  exact continuous_finsetSum _ (fun t _ => continuous_const.mul (hmono (words t)))

end YMUIC.Original30
