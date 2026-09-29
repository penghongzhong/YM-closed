import Mathlib

set_option autoImplicit false

/-!
# U2 root does not enter bulk placement entropy: Penrose + bounded roots

The only external combinatorial input used here is the pointwise hard-core
Penrose inequality
  |phi^T(Gamma)| <= number_of_allowed_spanning_trees(Gamma).

The theorem below proves internally that two external root factors bounded by
K contribute only K^2; they do not introduce any bulk placement sum.
The symmetry factor (e.g. 1/n!) and the bulk activity product are untouched.
-/

namespace YMUICV128.Section03.T007B

theorem bounded_external_roots_do_not_add_bulk_entropy
    {symFactor ursellAbs treeCount rootPAbs rootQAbs bulkAbs Kr : ℝ}
    (hsym : 0 ≤ symFactor)
    (hursell : 0 ≤ ursellAbs)
    (htree : 0 ≤ treeCount)
    (hrootP0 : 0 ≤ rootPAbs)
    (hrootQ0 : 0 ≤ rootQAbs)
    (hbulk : 0 ≤ bulkAbs)
    (hKr : 0 ≤ Kr)
    (hPenrose : ursellAbs ≤ treeCount)
    (hrootP : rootPAbs ≤ Kr)
    (hrootQ : rootQAbs ≤ Kr) :
    symFactor * ursellAbs * rootPAbs * rootQAbs * bulkAbs
      ≤
    Kr ^ 2 * (symFactor * treeCount * bulkAbs) := by
  have hU :
      symFactor * ursellAbs
        ≤ symFactor * treeCount :=
    mul_le_mul_of_nonneg_left hPenrose hsym
  have hRoots :
      rootPAbs * rootQAbs ≤ Kr * Kr := by
    calc
      rootPAbs * rootQAbs
          ≤ Kr * rootQAbs :=
        mul_le_mul_of_nonneg_right hrootP hrootQ0
      _ ≤ Kr * Kr :=
        mul_le_mul_of_nonneg_left hrootQ hKr
  have hPair :
      (symFactor * ursellAbs) * (rootPAbs * rootQAbs)
        ≤
      (symFactor * treeCount) * (Kr * Kr) := by
    exact mul_le_mul hU hRoots
      (mul_nonneg hrootP0 hrootQ0)
      (mul_nonneg hsym htree)
  have hAll :=
    mul_le_mul_of_nonneg_right hPair hbulk
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hAll

#print axioms bounded_external_roots_do_not_add_bulk_entropy

end YMUICV128.Section03.T007B
