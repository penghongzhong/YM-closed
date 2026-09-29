import Mathlib
import Section04.T012A_B08_Collar

set_option autoImplicit false

namespace YMUICV128.Section04.T012B
open T012A

theorem orbit_continuousOn {S : ℕ → Type*} [∀ j, TopologicalSpace (S j)]
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (U : (j : ℕ) → Set (S j)) (J : Set ℝ) (K : ℕ)
    (hiota : ContinuousOn iota J)
    (hR : ∀ j < K, ContinuousOn (R j) (U j))
    (hcollar : ∀ u ∈ J, ∀ j ≤ K, rgOrbit R iota j u ∈ U j) :
    ∀ j ≤ K, ContinuousOn (rgOrbit R iota j) J := by
  intro j
  induction j with
  | zero => intro hj; exact hiota
  | succ j ih =>
      intro hj
      have h := (hR j (by omega)).comp (ih (by omega))
        (fun u hu => hcollar u hu j (by omega))
      simpa only [rgOrbit] using h

theorem coordinates_continuousOn {S : ℕ → Type*} [∀ j, TopologicalSpace (S j)]
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (U : (j : ℕ) → Set (S j))
    (J : Set ℝ) (K : ℕ) (hiota : ContinuousOn iota J)
    (hR : ∀ j < K, ContinuousOn (R j) (U j))
    (hpi : ∀ j ≤ K, Continuous (pi j))
    (hcollar : ∀ u ∈ J, ∀ j ≤ K, rgOrbit R iota j u ∈ U j) :
    ∀ j ≤ K, ContinuousOn (rgCoordinate R iota pi j) J := by
  intro j hj
  exact (hpi j hj).comp_continuousOn (orbit_continuousOn R iota U J K hiota hR hcollar j hj)

theorem path_remainder_continuousOn {S : ℕ → Type*} [∀ j, TopologicalSpace (S j)]
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (U : (j : ℕ) → Set (S j))
    (J : Set ℝ) (K : ℕ) (Gamma C xw : ℝ) (hxw : 0 < xw)
    (hiota : ContinuousOn iota J)
    (hR : ∀ j < K, ContinuousOn (R j) (U j))
    (hpi : ∀ j ≤ K, Continuous (pi j))
    (hcollar : ∀ u ∈ J, ∀ j ≤ K,
      xw ≤ rgCoordinate R iota pi j u ∧ rgOrbit R iota j u ∈ U j) :
    ∀ j < K, ContinuousOn (pathRemainder R iota pi Gamma C j) J := by
  have hc := coordinates_continuousOn R iota pi U J K hiota hR hpi
    (fun u hu j hj => (hcollar u hu j hj).2)
  intro j hj
  have hnonzero : ∀ u ∈ J, rgCoordinate R iota pi j u ≠ 0 := by
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le hxw (hcollar u hu j (by omega)).1)
  exact (((hc (j + 1) (by omega)).sub (hc j (by omega))).add continuousOn_const).add
    (continuousOn_const.div (hc j (by omega)) hnonzero)

#print axioms orbit_continuousOn
#print axioms coordinates_continuousOn
#print axioms path_remainder_continuousOn

end YMUICV128.Section04.T012B
