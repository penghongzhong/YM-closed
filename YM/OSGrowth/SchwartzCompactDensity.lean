import YM.OSGrowth.DyadicSchwartzApproximation

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace YMUIC.OSGrowth

/-- Actual smooth compactly supported tests are dense in the full Schwartz
topology. This follows from the explicit dyadic approximants, without a
separate density assumption or any tensor-product identification. -/
theorem compact_support_schwartz_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E] :
    Dense {f : SchwartzMap E ℂ | HasCompactSupport (f : E → ℂ)} := by
  intro f
  obtain ⟨hs, ht⟩ := dyadic_schwartz_approximation f
  exact mem_closure_of_tendsto ht (Eventually.of_forall hs)

end YMUIC.OSGrowth
