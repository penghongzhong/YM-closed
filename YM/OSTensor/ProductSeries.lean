import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace YMUIC.OSTensor

/-- The mass of an absolutely summable nonnegative product family is the
product of its one-factor masses, with no dimension-dependent loss. -/
theorem product_series {I : Type*} (r : ℕ) (w : Fin r → I → ℝ)
    (hw : ∀ j i, 0 ≤ w j i) (hs : ∀ j, Summable (w j)) :
    HasSum (fun k : Fin r → I => ∏ j, w j (k j)) (∏ j, ∑' i, w j i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ht := ih (fun j => w j.succ) (fun j => hw j.succ) (fun j => hs j.succ)
    have hm : Summable (fun k : I × (Fin r → I) =>
        w 0 k.1 * ∏ j, w j.succ (k.2 j)) :=
      (hs 0).mul_of_nonneg ht.summable (hw 0)
        (fun k => Finset.prod_nonneg (fun j _ => hw j.succ (k j)))
    apply (Fin.consEquiv (fun _ : Fin (r + 1) => I)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv] using
      (hs 0).hasSum.mul ht hm

end YMUIC.OSTensor
