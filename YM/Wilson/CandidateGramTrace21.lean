import YM.Wilson.CandidateGramRoots21

set_option autoImplicit false
noncomputable section

namespace YMUIC.Wilson
open YMUICV128.Section03

/-!
# Exact classical cross-plaquette trace dictionary

For six actual SU(2) plaquettes at a shared basepoint, the independent
21-root candidate's Wilson-difference definition is IDENTICALLY equal
to the matrix trace of (U_i - I)(U_j - I). This exact identity is
needed before any continuum a^(-4) jet expansion is attempted.
It is not the classical or quantum RG estimate itself.
-/

abbrev GramMat2 := Matrix (Fin 2) (Fin 2) ℂ

theorem candidate_gram_root_trace_dictionary
    (U : GramPlaquette6 → SU2) (i j : GramPlaquette6) :
    candidateGramRoot U i j =
      -(Matrix.trace
        (((U i : GramMat2) - 1) * ((U j : GramMat2) - 1))).re / 2 := by
  have htrace :
      Matrix.trace
        (((U i : GramMat2) - 1) * ((U j : GramMat2) - 1)) =
        Matrix.trace ((U i : GramMat2) * (U j : GramMat2)) -
        Matrix.trace (U i : GramMat2) -
        Matrix.trace (U j : GramMat2) + 2 := by
    simp [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_one]
    ring
  have hcoe :
      ((U i * U j : SU2) : GramMat2) =
        (U i : GramMat2) * (U j : GramMat2) := rfl
  unfold candidateGramRoot wilsonRoot
  rw [hcoe, htrace]
  simp only [Complex.sub_re, Complex.add_re]
  norm_num
  ring

end YMUIC.Wilson
