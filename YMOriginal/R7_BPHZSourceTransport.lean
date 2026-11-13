import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.R7

/-- R7 arithmetic core for coefficientwise BPHZ.
If the ordinary fifth-order scale surplus is geometric with ratio q<1,
and source transport costs at most s^r per RG age with 0≤s≤1 after
normalizing by one extra L^{-r} factor, then the combined all-order
age series is summable. -/
theorem bphz_source_transport_summable
    (q s : ℝ) (r : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun m : ℕ => q ^ m * s ^ (r * m)) := by
  let a : ℝ := q * s ^ r
  have hsr0 : 0 ≤ s ^ r := pow_nonneg hs0 r
  have hsr1 : s ^ r ≤ 1 := pow_le_one₀ hs0 hs1
  have ha0 : 0 ≤ a := mul_nonneg hq0 hsr0
  have ha1 : a < 1 := by
    dsimp [a]
    calc
      q * s ^ r ≤ q * 1 := mul_le_mul_of_nonneg_left hsr1 hq0
      _ = q := by ring
      _ < 1 := hq1
  have hgeom : Summable (fun m : ℕ => a ^ m) :=
    summable_geometric_of_lt_one ha0 ha1
  simpa [a, mul_pow, pow_mul] using hgeom

/-- Pointwise version: the transport factor never enlarges the
underlying fifth-order geometric majorant once it has been normalized
to s≤1. -/
theorem bphz_source_transport_le
    (q s : ℝ) (r m : ℕ)
    (hq0 : 0 ≤ q) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    q ^ m * s ^ (r * m) ≤ q ^ m := by
  have hqpow : 0 ≤ q ^ m := pow_nonneg hq0 m
  have hspow0 : 0 ≤ s ^ (r * m) := pow_nonneg hs0 _
  have hspow1 : s ^ (r * m) ≤ 1 := pow_le_one₀ hs0 hs1
  calc
    q ^ m * s ^ (r * m) ≤ q ^ m * 1 :=
      mul_le_mul_of_nonneg_left hspow1 hqpow
    _ = q ^ m := by ring

#print axioms bphz_source_transport_summable
#print axioms bphz_source_transport_le

end YMUIC.R7
