import Mathlib

set_option autoImplicit false

namespace YMUICV128.Section04.T012C

theorem endpoint_clock_signs (Psi Phi : ℝ → ℝ)
    (a b xs xw M sigma eminus eplus : ℝ) (K : ℕ)
    (hmono : MonotoneOn Psi (Set.Ici xw)) (hsigma : 0 < sigma)
    (hxs : xw ≤ xs) (hminusmem : xw ≤ Phi a) (hplusmem : xw ≤ Phi b)
    (hbareminus : Psi a = (K : ℝ) + Psi xs - (M + sigma))
    (hbareplus : Psi b = (K : ℝ) + Psi xs + (M + sigma))
    (hclockminus : Psi (Phi a) - Psi a = -(K : ℝ) + eminus)
    (hclockplus : Psi (Phi b) - Psi b = -(K : ℝ) + eplus)
    (herrorMinus : |eminus| ≤ M) (herrorPlus : |eplus| ≤ M) :
    Phi a < xs ∧ xs < Phi b := by
  have hm : Psi (Phi a) < Psi xs := by
    have he := (abs_le.mp herrorMinus).2
    linarith
  have hp : Psi xs < Psi (Phi b) := by
    have he := (abs_le.mp herrorPlus).1
    linarith
  constructor
  · by_contra hf
    have h := hmono hxs hminusmem (le_of_not_gt hf)
    linarith
  · by_contra hf
    have h := hmono hplusmem hxs (le_of_not_gt hf)
    linarith

#print axioms endpoint_clock_signs

end YMUICV128.Section04.T012C
