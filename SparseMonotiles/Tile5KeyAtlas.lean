module

public import SparseMonotiles.AtlasBindings5
public import SparseMonotiles.AtlasCertificates5

@[expose] public section

/-! Concrete consequences of the checked exact exposed-facet/key atlas.
These theorems retain the actual closure around a dent difference. They do not
assert a complete ridge inventory, tiling-sector classification, or registration. -/
namespace SparseMonotiles

open Contact
open Canonical
open Set Filter
open scoped Topology

private theorem supportValid5 : IndexedData5.geometry.SupportValid :=
  IndexedGeometry.supportValid_of_atlasValidAt (by decide) atlas5_checked

private theorem exposed5 (i : Fin 160) :
    ¬ IsChairCell (IndexedData5.geometry.facet i).neighbor :=
  (atlas5_checked i).1

/-- Distinct exact keys have disjoint closed coordinate supports. -/
theorem T5_keySupports_disjoint {k l : KeyData 5}
    (hk : k ∈ keys5) (hl : l ∈ keys5) (hne : k ≠ l) :
    Disjoint (keyCoordinateSupport k) (keyCoordinateSupport l) :=
  IndexedGeometry.literal_coordinateSupports_disjoint supportValid5
    IndexedData5.facet_injective IndexedData5.owned_checked exposed5
    everyKey5_in_atlas hk hl hne

/-- The complete closed pyramids, including their bases and apices, are disjoint. -/
theorem T5_keySolids_disjoint {k l : KeyData 5}
    (hk : k ∈ keys5) (hl : l ∈ keys5) (hne : k ≠ l) :
    Disjoint (keySolid k) (keySolid l) :=
  (T5_keySupports_disjoint hk hl hne).mono
    (keySolid_subset_coordinateSupport _) (keySolid_subset_coordinateSupport _)

/-- Every exact key is contained in its checked exposed integer-facet collar. -/
theorem T5_key_has_exposed_collar {k : KeyData 5} (hk : k ∈ keys5) :
    ∃ i : Fin 160, IsChairCell (IndexedData5.geometry.facet i).cell ∧
      ¬ IsChairCell (IndexedData5.geometry.facet i).neighbor ∧
      keySolid k ⊆ gridFacetCollar (IndexedData5.geometry.facet i).gridFacet := by
  obtain ⟨i, b, hb, he⟩ := everyKey5_in_atlas k hk
  refine ⟨i, IndexedData5.owned_checked i, exposed5 i, ?_⟩
  rw [← he]
  exact BoxKey.keySolid_subset_collar supportValid5.1 (supportValid5.2.1 i b hb)

/-- Around every point of a key's support, all other exact keys are absent. -/
theorem T5_key_isolated {k : KeyData 5} (hk : k ∈ keys5)
    {p : Point 5} (hp : p ∈ keyCoordinateSupport k) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ keys5, j ≠ k → x ∉ keySolid j :=
  IndexedGeometry.key_isolation supportValid5 IndexedData5.facet_injective
    IndexedData5.owned_checked exposed5 everyKey5_in_atlas hk hp

/-- The actual body's germ is an exposed halfspace with exactly this signed key.
For dents the final closure is essential and remains in the conclusion. -/
theorem T5_isolated_key_halfspace {k : KeyData 5} (hk : k ∈ keys5)
    {p : Point 5} (hp : p ∈ keyCoordinateSupport k) :
    ∃ i : Fin 160, LocalSetEq p T5
      (closure (keyReplacement (IndexedData5.geometry.facet i).inwardHalfspace
        (keySolid k) k.bump)) :=
  IndexedGeometry.localSetEq_body_isolated_halfspace supportValid5
    IndexedData5.facet_injective IndexedData5.owned_checked exposed5
    everyKey5_in_atlas hk hp

/-- Every point has one of the two exact local material models. -/
theorem T5_local_body_inventory (p : Point 5) :
    LocalSetEq p T5 (carrier 5) ∨
      ∃ k ∈ keys5, ∃ i : Fin 160, LocalSetEq p T5
        (closure (keyReplacement (IndexedData5.geometry.facet i).inwardHalfspace
          (keySolid k) k.bump)) :=
  IndexedGeometry.localSetEq_body_inventory supportValid5
    IndexedData5.facet_injective IndexedData5.owned_checked exposed5
    everyKey5_in_atlas p

/-- The corresponding complete support-level boundary inventory. -/
theorem T5_local_boundary_inventory (p : Point 5) :
    LocalSetEq p (frontier T5) (frontier (carrier 5)) ∨
      ∃ k ∈ keys5, ∃ i : Fin 160, LocalSetEq p (frontier T5)
        (frontier (closure
          (keyReplacement (IndexedData5.geometry.facet i).inwardHalfspace
            (keySolid k) k.bump))) :=
  IndexedGeometry.localSetEq_frontier_body_inventory supportValid5
    IndexedData5.facet_injective IndexedData5.owned_checked exposed5
    everyKey5_in_atlas p

#print axioms T5_local_body_inventory
#print axioms T5_local_boundary_inventory

#print axioms T5_keySupports_disjoint
#print axioms T5_keySolids_disjoint
#print axioms T5_key_has_exposed_collar
#print axioms T5_key_isolated
#print axioms T5_isolated_key_halfspace

end SparseMonotiles
