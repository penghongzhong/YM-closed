import Mathlib
import Section04.T012A_B08_Collar
import Section04.T012B_B08_EndpointContinuity
import Section04.T012C_B08_SignBracket
import Section04.T012D_B08_IntermediateValue
import Section04.T012E_B08_FirstExit

set_option autoImplicit false

namespace YMUICV128.Section04.T012F
open T012A

/-- Final assembly with the actual full-state orbit; all earlier nodes remain explicit. -/
theorem phase_lock_from_certified_bracket {S : ℕ → Type*} [∀ j, TopologicalSpace (S j)]
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (U : (j : ℕ) → Set (S j))
    (K : ℕ) (a b xs xw delta : ℝ) (hab : a ≤ b) (hd : 0 < delta)
    (hiota : ContinuousOn iota (Set.Icc a b))
    (hR : ∀ j < K, ContinuousOn (R j) (U j))
    (hpi : ∀ j ≤ K, Continuous (pi j))
    (hcollar : ∀ u ∈ Set.Icc a b, ∀ j ≤ K,
      xw ≤ rgCoordinate R iota pi j u ∧ rgOrbit R iota j u ∈ U j)
    (hsign : rgCoordinate R iota pi K a < xs ∧ xs < rgCoordinate R iota pi K b)
    (hstep : ∀ u ∈ Set.Icc a b, ∀ j < K,
      rgCoordinate R iota pi (j + 1) u ≤ rgCoordinate R iota pi j u - delta) :
    ∃ u ∈ Set.Ioo a b,
      (∀ j ≤ K, rgOrbit R iota j u ∈ U j) ∧
      (∀ j < K, xs < rgCoordinate R iota pi j u) ∧ rgCoordinate R iota pi K u = xs := by
  have hcont := T012B.coordinates_continuousOn R iota pi U (Set.Icc a b) K
    hiota hR hpi (fun u hu j hj => (hcollar u hu j hj).2) K le_rfl
  obtain ⟨u, hu, hhit⟩ := T012D.endpoint_shooting (rgCoordinate R iota pi K)
    a b xs hab hcont hsign.1 hsign.2
  have huclosed : u ∈ Set.Icc a b := ⟨hu.1.le, hu.2.le⟩
  have he := T012E.first_exit_exclusion (fun j => rgCoordinate R iota pi j u) K xs delta hd
    (hstep u huclosed) hhit
  exact ⟨u, hu, (fun j hj => (hcollar u huclosed j hj).2), he.1, he.2⟩

/-- The collar and signs are derived, not assumed, from the prefix-clock inputs. -/
theorem phase_lock_from_prefix_inputs {S : ℕ → Type*} [∀ j, TopologicalSpace (S j)]
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (U : (j : ℕ) → Set (S j))
    (Psi : ℝ → ℝ) (eps : ℕ → ℝ → ℝ)
    (K : ℕ) (a b xw xs Gplus M sigma delta : ℝ)
    (hab : a ≤ b) (hd : 0 < delta) (hsigma : 0 < sigma)
    (hmono : MonotoneOn Psi (Set.Ici xw)) (hGp : 0 ≤ Gplus)
    (ha : xw ≤ a) (hxs : xw ≤ xs)
    (hbare : ∀ u ∈ Set.Icc a b, rgCoordinate R iota pi 0 u = u)
    (haminus : Psi a = (K : ℝ) + Psi xs - (M + sigma))
    (hbplus : Psi b = (K : ℝ) + Psi xs + (M + sigma))
    (hsep : (M + sigma) + M < Psi xs - Psi (xw + Gplus))
    (hupper : ∀ u ∈ Set.Icc a b, ∀ n < K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) →
      rgCoordinate R iota pi n u - rgCoordinate R iota pi (n + 1) u ≤ Gplus)
    (hclock : ∀ u ∈ Set.Icc a b, ∀ n ≤ K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) →
      Psi (rgCoordinate R iota pi n u) - Psi (rgCoordinate R iota pi 0 u) =
        -(n : ℝ) + eps n u ∧ |eps n u| ≤ M)
    (hpreserve : ∀ u ∈ Set.Icc a b, ∀ n ≤ K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) → rgOrbit R iota n u ∈ U n)
    (hlower : ∀ u ∈ Set.Icc a b, ∀ n < K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) →
      rgCoordinate R iota pi (n + 1) u ≤ rgCoordinate R iota pi n u - delta)
    (hiota : ContinuousOn iota (Set.Icc a b))
    (hR : ∀ j < K, ContinuousOn (R j) (U j))
    (hpi : ∀ j ≤ K, Continuous (pi j)) :
    ∃ u ∈ Set.Ioo a b,
      (∀ j ≤ K, rgOrbit R iota j u ∈ U j) ∧
      (∀ j < K, xs < rgCoordinate R iota pi j u) ∧ rgCoordinate R iota pi K u = xs := by
  have hc := full_state_collar R iota pi U Psi eps K a b xw xs Gplus M (M + sigma)
    hmono hGp ha hbare haminus hsep hupper hclock hpreserve
  have haJ : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbJ : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  obtain ⟨hem, hbm⟩ := hclock a haJ K le_rfl (fun m hm => (hc a haJ m hm).1)
  obtain ⟨hep, hbp⟩ := hclock b hbJ K le_rfl (fun m hm => (hc b hbJ m hm).1)
  rw [hbare a haJ] at hem
  rw [hbare b hbJ] at hep
  have hs := T012C.endpoint_clock_signs Psi (rgCoordinate R iota pi K)
    a b xs xw M sigma (eps K a) (eps K b) K hmono hsigma hxs
    (hc a haJ K le_rfl).1 (hc b hbJ K le_rfl).1 haminus hbplus hem hep hbm hbp
  apply phase_lock_from_certified_bracket R iota pi U K a b xs xw delta hab hd
    hiota hR hpi hc hs
  intro u hu j hj
  exact hlower u hu j hj (fun m hm => (hc u hu m (by omega)).1)

#print axioms phase_lock_from_certified_bracket
#print axioms phase_lock_from_prefix_inputs

end YMUICV128.Section04.T012F
