import YMOriginal.Original24_ActualHardCoreGraph

set_option autoImplicit false
noncomputable section
namespace YMUIC.Original24

/-!
# Physical 4D periodic contact reversibility: EXACT KP = hard-core graph

The U2 periodic KP recursion in Original24_PeriodicKPFiniteTree has
a directed-looking first-child definition:
  child(Y of X) <-> supp(Y) meets N_chi(supp(X)).

The Penrose/FP hard-core cluster graph requires a SYMMETRIC
incompatibility.  This module proves the exact reversibility of the
literal four-dimensional ZMod N chi-neighborhood, even when the torus
wraps and χ is larger than N.  Consequently the old KP children
ARE EXACTLY the neighbors in the hard-core species graph, not an
unverified combinatorial dictionary or a new arbitrary contact rule.
-/

/-- Every actual 4D periodic chi-contact neighborhood is symmetric.
The inverse offset is 2*chi - offset in each of four coordinates. -/
theorem four_dim_periodic_neighborhood_symm
    (N chi : ℕ) (x y : PeriodicBlock N) :
    y ∈ fourDimPeriodicNeighborhood N chi x ↔
      x ∈ fourDimPeriodicNeighborhood N chi y := by
  classical
  have hflip (x y : PeriodicBlock N) :
      y ∈ fourDimPeriodicNeighborhood N chi x →
        x ∈ fourDimPeriodicNeighborhood N chi y := by
    intro hy
    unfold fourDimPeriodicNeighborhood at hy ⊢
    obtain ⟨offset, _ho, hoff⟩ := Finset.mem_image.mp hy
    let opposite : Fin 4 → Fin (2 * chi + 1) := fun i =>
      ⟨2 * chi - (offset i).val, by
        have hi := (offset i).isLt
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨opposite, Finset.mem_univ _, ?_⟩
    funext i
    have hxy : x i + ((offset i).val : ZMod N) -
        (chi : ZMod N) = y i := by
      have heval := congrArg (fun z : PeriodicBlock N => z i) hoff
      simpa only [fourDimPeriodicShift] using heval
    have hbound : (offset i).val ≤ 2 * chi := by
      have hi := (offset i).isLt
      omega
    have hcast : ((2 * chi - (offset i).val : ℕ) : ZMod N) =
        (2 : ZMod N) * (chi : ZMod N) -
          ((offset i).val : ZMod N) := by
      rw [Nat.cast_sub hbound]
      push_cast
      ring
    change y i + ((opposite i).val : ZMod N) -
      (chi : ZMod N) = x i
    change y i + ((2 * chi - (offset i).val : ℕ) : ZMod N) -
      (chi : ZMod N) = x i
    rw [hcast, ← hxy]
    ring
  exact ⟨hflip x y, hflip y x⟩

/-- Actual U2 first-child periodic contact is reversible on true
finite polymer supports; this includes arbitrary torus wrap-around. -/
theorem actual_periodic_polymer_children_symm
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (X Y : Γ) :
    Y ∈ actualPeriodicPolymerChildren N chi support X ↔
      X ∈ actualPeriodicPolymerChildren N chi support Y := by
  classical
  have hflip (X Y : Γ)
      (h : Y ∈ actualPeriodicPolymerChildren N chi support X) :
      X ∈ actualPeriodicPolymerChildren N chi support Y := by
    change Y ∈ actualContactRoot (support X)
      (fourDimPeriodicNeighborhood N chi) support at h
    obtain ⟨_, ⟨v, hv, hYv⟩⟩ := Finset.mem_filter.mp h
    change v ∈ (support X).biUnion
      (fourDimPeriodicNeighborhood N chi) at hv
    obtain ⟨u, hXu, hvu⟩ := Finset.mem_biUnion.mp hv
    change X ∈ actualContactRoot (support Y)
      (fourDimPeriodicNeighborhood N chi) support
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨u, ?_, hXu⟩⟩
    change u ∈ (support Y).biUnion
      (fourDimPeriodicNeighborhood N chi)
    exact Finset.mem_biUnion.mpr
      ⟨v, hYv, (four_dim_periodic_neighborhood_symm N chi u v).mp hvu⟩
  exact ⟨hflip X Y, hflip Y X⟩

/-- THE SAME relation as the existing U2 finite-height child
recursion is the actual hard-core graph adjacency, with the
only difference that graph loops are forbidden by definition.
Hence no second/speculative incompatibility geometry is introduced. -/
theorem actual_hardcore_graph_adj_iff_U2_child
    {Γ : Type*} [Fintype Γ]
    (N chi : ℕ) (support : Γ → Finset (PeriodicBlock N))
    (X Y : Γ) :
    (actualPeriodicHardCoreSpeciesGraph N chi support).Adj X Y ↔
      X ≠ Y ∧ Y ∈ actualPeriodicPolymerChildren N chi support X := by
  rw [actual_periodic_hardcore_species_adj]
  constructor
  · rintro ⟨hne, hc⟩
    rcases hc with heq | hc | hc
    · exact (hne heq).elim
    · exact ⟨hne,
        (actual_periodic_polymer_children_symm N chi support Y X).mp hc⟩
    · exact ⟨hne, hc⟩
  · rintro ⟨hne, hc⟩
    exact ⟨hne, Or.inr (Or.inr hc)⟩

end YMUIC.Original24
