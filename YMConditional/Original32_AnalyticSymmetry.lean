import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace YMUIC.SchwingerSymmetry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual n-th Frechet derivative of the same analytic source functional,
evaluated at source zero. No symmetry is included in this definition. -/
def sourceDerivative (n : ℕ) (Z : E → ℂ) (v : Fin n → E) : ℂ :=
  iteratedFDeriv ℂ n Z 0 v

/-- Native Mathlib analytic calculus proves the equality for every order,
including repeated directions and order zero. No finite-cutoff symmetry
certificate or unformalized differentiation interface is assumed. -/
theorem analytic_source_derivative_permutation
    (Z : E → ℂ) (hZ : AnalyticAt ℂ Z 0)
    (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    sourceDerivative n Z (v ∘ σ) = sourceDerivative n Z v := by
  exact hZ.contDiffAt.iteratedFDeriv_comp_perm v σ

/-- A cutoff-dependent renormalized source map is applied to each insertion.
The map must be the SAME for all slots at that cutoff; no norm bound,
invertibility or convergence of source transformations is required here. -/
def cutoffSchwinger {Test : Type*} (Z : E → ℂ) (liftSource : Test → E)
    (n : ℕ) (f : Fin n → Test) : ℂ :=
  sourceDerivative n Z (fun a => liftSource (f a))

theorem cutoff_schwinger_permutation {Test : Type*}
    (Z : E → ℂ) (hZ : AnalyticAt ℂ Z 0) (liftSource : Test → E)
    (n : ℕ) (f : Fin n → Test) (σ : Equiv.Perm (Fin n)) :
    cutoffSchwinger Z liftSource n (f ∘ σ) =
      cutoffSchwinger Z liftSource n f := by
  exact analytic_source_derivative_permutation Z hZ n
    (fun a => liftSource (f a)) σ

end YMUIC.SchwingerSymmetry
