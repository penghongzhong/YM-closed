import Mathlib

set_option autoImplicit false

/-!
Standalone certificates for v133 §1.

TeX objects:
  a_j = L^j a_0,
  g_j > 0,
  x_j = g_j^{-2},
  tr_B(M) = (1/2) Tr(M).

This file verifies only elementary definitional/positivity content.
-/

namespace YMUICV128.Section01

def latticeSpacing (L : ℕ) (a0 : ℝ) (j : ℕ) : ℝ :=
  (L : ℝ) ^ j * a0

theorem latticeSpacing_pos
    {L j : ℕ} {a0 : ℝ}
    (hL : 2 ≤ L) (ha0 : 0 < a0) :
    0 < latticeSpacing L a0 j := by
  unfold latticeSpacing
  have hLnat : 0 < L := by omega
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hLnat
  exact mul_pos (pow_pos hLreal j) ha0

noncomputable def inverseCoupling (g : ℝ) : ℝ :=
  (g⁻¹) ^ 2

theorem inverseCoupling_pos
    {g : ℝ} (hg : 0 < g) :
    0 < inverseCoupling g := by
  unfold inverseCoupling
  positivity

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

def plaquetteHolonomy
    (U1 U2 U3 U4 : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  U1 * U2 * U3 * U4

noncomputable def normalizedTrace2
    (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace M

#print axioms latticeSpacing_pos
#print axioms inverseCoupling_pos

end YMUICV128.Section01
