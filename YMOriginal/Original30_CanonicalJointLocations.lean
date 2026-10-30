import YMOriginal.Original30_AllVolumeJointWilson

set_option autoImplicit false
noncomputable section

namespace YMUIC.Original30
open YMUIC.Wilson
open YMUIC.Original24
open YMUICV128.Section03

/-!
# Exact physical 4r joint coordinate dictionary, no abstract geometry

The j-th 4D site is located at the four coordinates 4*j,...,4*j+3
of the actual (4r)-dimensional joint Schwartz test argument.
The coordinate comparison ||x_j|| <= ||(x_1,...,x_r)|| is then proved
using the exact Euclidean sum-of-squares norm and finite image sums.

This removes the only remaining geometry hypothesis from the previous
all-volume JOINT bare Wilson theorem. Neither source normalization
a^-d nor true RG/continuum convergence is asserted.
-/

/-- Physical coordinate j,k inside the actual 4r-dimensional joint test. -/
def actualJointIndex (r : ℕ) (j : Fin r) (k : Fin 4) :
    Fin (4 * r) :=
  ⟨4 * j.val + k.val, by omega⟩

/-- True concatenated physical lattice positions for arbitrary r. -/
def actualJointSpatialLocation (r N : ℕ) (a : ℝ)
    (tuple : Fin r → TrueSpatialPlaquettes N) :
    EuclideanSpace ℝ (Fin (4 * r)) :=
  WithLp.toLp 2
    (fun i : Fin (4 * r) =>
      a * ((tuple ⟨i.val / 4, by omega⟩).2
         ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩ : ℝ))

/-- The exact j,k-th physical coordinate, with no scaling mismatch. -/
theorem actual_joint_spatial_coordinate (r N : ℕ) (a : ℝ)
    (tuple : Fin r → TrueSpatialPlaquettes N)
    (j : Fin r) (k : Fin 4) :
    actualJointSpatialLocation r N a tuple (actualJointIndex r j k) =
      (trueLatticeSitePosition a (tuple j).2) k := by
  have hdiv : (4 * j.val + k.val) / 4 = j.val := by omega
  have hmod : (4 * j.val + k.val) % 4 = k.val := by omega
  simp [actualJointSpatialLocation, actualJointIndex,
    trueLatticeSitePosition, hdiv, hmod]

/-- Every 4-dimensional block embeds injectively into the full 4r
joint coordinate family; no dimension-dependent norm factor. -/
theorem actual_joint_index_injective (r : ℕ) (j : Fin r) :
    Function.Injective (actualJointIndex r j) := by
  intro k l hkl
  have h : 4 * j.val + k.val = 4 * j.val + l.val := by
    simpa [actualJointIndex] using congrArg Fin.val hkl
  exact Fin.ext (by omega)

/-- The exact 4D physical site norm is bounded by the norm of the
canonical joint 4r-dimensional position, with constant ONE. -/
theorem actual_joint_spatial_norm_dominates_component
    (r N : ℕ) (a : ℝ)
    (tuple : Fin r → TrueSpatialPlaquettes N)
    (j : Fin r) :
    ‖trueLatticeSitePosition a (tuple j).2‖ ≤
      ‖actualJointSpatialLocation r N a tuple‖ := by
  classical
  let x : Space4 := trueLatticeSitePosition a (tuple j).2
  let y : EuclideanSpace ℝ (Fin (4 * r)) :=
    actualJointSpatialLocation r N a tuple
  let g : Fin 4 → Fin (4 * r) := actualJointIndex r j
  have hinj : Function.Injective g :=
    actual_joint_index_injective r j
  have hcoord (k : Fin 4) : x k = y (g k) := by
    dsimp [x, y, g]
    exact (actual_joint_spatial_coordinate r N a tuple j k).symm
  have hsumCoord :
      (∑ k : Fin 4, (x k) ^ 2) =
      (∑ k : Fin 4, (y (g k)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcoord k]
  have himage :
      (∑ k : Fin 4, (y (g k)) ^ 2) =
      ∑ i ∈ ((Finset.univ : Finset (Fin 4)).image g),
        (y i) ^ 2 := by
    simp [Finset.sum_image hinj.injOn]
  have hsubset :
      (∑ i ∈ ((Finset.univ : Finset (Fin 4)).image g),
        (y i) ^ 2) ≤
      ∑ i : Fin (4 * r), (y i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro i hi hi'
      exact sq_nonneg _
  have hSq : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ k : Fin 4, (x k) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ = ∑ k : Fin 4, (y (g k)) ^ 2 := hsumCoord
      _ = ∑ i ∈ ((Finset.univ : Finset (Fin 4)).image g),
            (y i) ^ 2 := himage
      _ ≤ ∑ i : Fin (4 * r), (y i) ^ 2 := hsubset
      _ = ‖y‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq

/-- ACTUAL all-volume, all-cutoff, all-r joint Schwartz bare SU(2)
Wilson source estimate with no abstract source-location geometry input. -/
theorem actual_joint_bare_wilson_all_volume_canonical
    {W T : Type*} [Fintype T]
    (r N : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (U : TrueSpatialPlaquettes N → W → SU2)
    (words : TrueSpatialPlaquettes N → T → List (List W))
    (coeff : TrueSpatialPlaquettes N → T → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbudget : ∀ p,
      actualWilsonPolynomialBudget (words p) (coeff p) ≤ K)
    (f : YMUIC.Original34.JointTest r) :
    ‖actualWordJointCutoff r
      (fun _ : TrueSpatialPlaquettes N => ((a ^ 4 : ℝ) : ℂ))
      U words coeff (actualJointSpatialLocation r N a) f‖ ≤
      (24576 * K) ^ r *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (8 * r) 0 f) := by
  exact actual_joint_bare_wilson_all_volume_bound
    r N a ha ha1 U words coeff
    (actualJointSpatialLocation r N a)
    (fun tuple j =>
      actual_joint_spatial_norm_dominates_component r N a tuple j)
    K hK hbudget f

end YMUIC.Original30
