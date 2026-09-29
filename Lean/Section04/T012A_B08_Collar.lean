import Mathlib

set_option autoImplicit false

/-!
B08 finite-horizon collar. The scalar first-exit argument is internal.
Full-state preservation is an explicit published-interface hypothesis, not
an internally re-proved RG theorem. No endpoint hit or phase lock is assumed.
-/
namespace YMUICV128.Section04.T012A

noncomputable def rgOrbit {S : ℕ → Type*}
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0) :
    (j : ℕ) → ℝ → S j
  | 0, u => iota u
  | j + 1, u => R j (rgOrbit R iota j u)

noncomputable def rgCoordinate {S : ℕ → Type*}
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  pi j (rgOrbit R iota j u)

noncomputable def pathRemainder {S : ℕ → Type*}
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (Gamma C : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  rgCoordinate R iota pi (j + 1) u - rgCoordinate R iota pi j u +
    Gamma + C / rgCoordinate R iota pi j u

theorem prefix_clock_collar (Psi : ℝ → ℝ) (x eps : ℕ → ℝ)
    (K : ℕ) (xw xs Gplus M Delta : ℝ)
    (hmono : MonotoneOn Psi (Set.Ici xw)) (hGp : 0 ≤ Gplus)
    (hinit : xw ≤ x 0)
    (hinitclock : (K : ℝ) + Psi xs - Delta ≤ Psi (x 0))
    (hsep : Delta + M < Psi xs - Psi (xw + Gplus))
    (hupper : ∀ n < K, (∀ m ≤ n, xw ≤ x m) → x n - x (n + 1) ≤ Gplus)
    (hclock : ∀ n ≤ K, (∀ m ≤ n, xw ≤ x m) →
      Psi (x n) - Psi (x 0) = -(n : ℝ) + eps n ∧ |eps n| ≤ M) :
    ∀ j ≤ K, xw ≤ x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      cases j with
      | zero => exact hinit
      | succ n =>
          have hp : ∀ m ≤ n, xw ≤ x m := by
            intro m hm
            exact ih m (by omega) (by omega)
          by_contra hf
          have hexit : x (n + 1) < xw := lt_of_not_ge hf
          have hu := hupper n (by omega) hp
          have hxn : x n ≤ xw + Gplus := by linarith
          have hc := hmono (hp n le_rfl) (by change xw ≤ xw + Gplus; linarith) hxn
          obtain ⟨hid, he⟩ := hclock n (by omega) hp
          have hel := (abs_le.mp he).1
          have hn : (n : ℝ) < (K : ℝ) := by exact_mod_cast (show n < K by omega)
          linarith

/-- Explicit RG-state assembly over the published full-state preservation interface. -/
theorem full_state_collar {S : ℕ → Type*}
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (U : (j : ℕ) → Set (S j))
    (Psi : ℝ → ℝ) (eps : ℕ → ℝ → ℝ)
    (K : ℕ) (a b xw xs Gplus M Delta : ℝ)
    (hmono : MonotoneOn Psi (Set.Ici xw)) (hGp : 0 ≤ Gplus)
    (ha : xw ≤ a)
    (hbare : ∀ u ∈ Set.Icc a b, rgCoordinate R iota pi 0 u = u)
    (haminus : Psi a = (K : ℝ) + Psi xs - Delta)
    (hsep : Delta + M < Psi xs - Psi (xw + Gplus))
    (hupper : ∀ u ∈ Set.Icc a b, ∀ n < K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) →
      rgCoordinate R iota pi n u - rgCoordinate R iota pi (n + 1) u ≤ Gplus)
    (hclock : ∀ u ∈ Set.Icc a b, ∀ n ≤ K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) →
      Psi (rgCoordinate R iota pi n u) - Psi (rgCoordinate R iota pi 0 u) =
        -(n : ℝ) + eps n u ∧ |eps n u| ≤ M)
    (hpreserve : ∀ u ∈ Set.Icc a b, ∀ n ≤ K,
      (∀ m ≤ n, xw ≤ rgCoordinate R iota pi m u) → rgOrbit R iota n u ∈ U n) :
    ∀ u ∈ Set.Icc a b, ∀ j ≤ K,
      xw ≤ rgCoordinate R iota pi j u ∧ rgOrbit R iota j u ∈ U j := by
  intro u hu
  have hu0 : xw ≤ rgCoordinate R iota pi 0 u := by rw [hbare u hu]; exact ha.trans hu.1
  have hic : (K : ℝ) + Psi xs - Delta ≤ Psi (rgCoordinate R iota pi 0 u) := by
    rw [hbare u hu, ← haminus]
    exact hmono ha (ha.trans hu.1) hu.1
  have hxall := prefix_clock_collar Psi (fun j => rgCoordinate R iota pi j u)
    (fun j => eps j u) K xw xs Gplus M Delta hmono hGp hu0 hic hsep
    (hupper u hu) (hclock u hu)
  intro j hj
  exact ⟨hxall j hj, hpreserve u hu j hj (fun m hm => hxall m (by omega))⟩

theorem path_remainder_recursion {S : ℕ → Type*}
    (R : (j : ℕ) → S j → S (j + 1)) (iota : ℝ → S 0)
    (pi : (j : ℕ) → S j → ℝ) (Gamma C : ℝ) (j : ℕ) (u : ℝ) :
    rgCoordinate R iota pi (j + 1) u = rgCoordinate R iota pi j u - Gamma -
      C / rgCoordinate R iota pi j u + pathRemainder R iota pi Gamma C j u := by
  unfold pathRemainder
  ring

#print axioms prefix_clock_collar
#print axioms full_state_collar
#print axioms path_remainder_recursion

end YMUICV128.Section04.T012A
