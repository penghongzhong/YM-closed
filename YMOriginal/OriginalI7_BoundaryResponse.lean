import Mathlib

set_option autoImplicit false
noncomputable section

namespace YMUIC.I7Boundary

/-!
# Actual-cube *sufficient condition* from one-exterior-link response

For the 4D SU2 forest-gauge cube of side 2*m, Proposition 260 in
Bhattacharjee--Bhattacharya--Lockwood--Romanov (2026) gives, for every
period-two exterior class c,

  sum_(j in c outside V) b(V,j) <= 10*m^3 - 2*m^2,

where b(V,j) counts sharing-plaquette contacts.

The following theorem is exact REAL ARITHMETIC for arbitrary finite
index classes. It isolates the ONLY new analytical hypothesis needed
to obtain D(2m,1/2): for the actual physical Wilson specification,

  C_(V,j) <= (m/20) * b(V,j).

The corresponding model-dependent Wasserstein inequality is NOT proved
here; nor is the geometry count re-proved for the actual forest gauge
in this file. This is not a physical I7 or mass-gap theorem.
-/

/-- Any actual cube response obeying at most m/20 per contact
satisfies the exact averaged Dobrushin--Shlosman budget with alpha=1/2.
The geometry premise is explicit for every residue/direction class. -/
theorem cube_half_from_contact_response
    {Class Link : Type*}
    (extClass : Class → Finset Link)
    (contacts response : Link → ℝ)
    (m : ℝ) (hm : 0 ≤ m)
    (hContacts : ∀ c,
      (∑ j ∈ extClass c, contacts j) ≤ 10 * m ^ 3 - 2 * m ^ 2)
    (hResponse : ∀ j, response j ≤ (m / 20) * contacts j) :
    ∀ c, (∑ j ∈ extClass c, response j) ≤ (1 / 2 : ℝ) * m ^ 4 := by
  intro c
  have hFactor : 0 ≤ m / 20 := div_nonneg hm (by norm_num)
  have hTerm :
      (∑ j ∈ extClass c, response j) ≤
        (m / 20) * (∑ j ∈ extClass c, contacts j) := by
    calc
      _ ≤ ∑ j ∈ extClass c, (m / 20) * contacts j :=
        Finset.sum_le_sum (fun j _ => hResponse j)
      _ = _ := by rw [Finset.mul_sum]
  have hCount :
      (m / 20) * (∑ j ∈ extClass c, contacts j) ≤
        (m / 20) * (10 * m ^ 3 - 2 * m ^ 2) :=
    mul_le_mul_of_nonneg_left (hContacts c) hFactor
  have hIdentity :
      (m / 20) * (10 * m ^ 3 - 2 * m ^ 2) =
        (1 / 2 : ℝ) * m ^ 4 - m ^ 3 / 10 := by ring
  have hCubic : 0 ≤ m ^ 3 / 10 :=
    div_nonneg (pow_nonneg hm 3) (by norm_num)
  calc
    (∑ j ∈ extClass c, response j)
        ≤ (m / 20) * (∑ j ∈ extClass c, contacts j) := hTerm
    _ ≤ (m / 20) * (10 * m ^ 3 - 2 * m ^ 2) := hCount
    _ = (1 / 2 : ℝ) * m ^ 4 - m ^ 3 / 10 := hIdentity
    _ ≤ (1 / 2 : ℝ) * m ^ 4 := sub_le_self _ hCubic

#print axioms cube_half_from_contact_response

end YMUIC.I7Boundary
