module

public import SparseMonotiles.AtlasBindings7
public import SparseMonotiles.AtlasCertificates7

@[expose] public section

/-! Concrete consequences of the checked exact exposed-facet/key atlas.
These theorems retain the actual closure around a dent difference. They do not
assert a complete ridge inventory, tiling-sector classification, or registration. -/
namespace SparseMonotiles

open Contact
open Canonical
open Set Filter
open scoped Topology

private theorem supportValid7 : IndexedData7.geometry.SupportValid :=
  IndexedGeometry.supportValid_of_atlasValidAt (by decide) atlas7_checked

private theorem exposed7 (i : Fin 896) :
    ¬ IsChairCell (IndexedData7.geometry.facet i).neighbor :=
  (atlas7_checked i).1

/-- Distinct exact keys have disjoint closed coordinate supports. -/
theorem T7_keySupports_disjoint {k l : KeyData 7}
    (hk : k ∈ keys7) (hl : l ∈ keys7) (hne : k ≠ l) :
    Disjoint (keyCoordinateSupport k) (keyCoordinateSupport l) :=
  IndexedGeometry.literal_coordinateSupports_disjoint supportValid7
    IndexedData7.facet_injective IndexedData7.owned_checked exposed7
    everyKey7_in_atlas hk hl hne

/-- The complete closed pyramids, including their bases and apices, are disjoint. -/
theorem T7_keySolids_disjoint {k l : KeyData 7}
    (hk : k ∈ keys7) (hl : l ∈ keys7) (hne : k ≠ l) :
    Disjoint (keySolid k) (keySolid l) :=
  (T7_keySupports_disjoint hk hl hne).mono
    (keySolid_subset_coordinateSupport _) (keySolid_subset_coordinateSupport _)

/-- Every exact key is contained in its checked exposed integer-facet collar. -/
theorem T7_key_has_exposed_collar {k : KeyData 7} (hk : k ∈ keys7) :
    ∃ i : Fin 896, IsChairCell (IndexedData7.geometry.facet i).cell ∧
      ¬ IsChairCell (IndexedData7.geometry.facet i).neighbor ∧
      keySolid k ⊆ gridFacetCollar (IndexedData7.geometry.facet i).gridFacet := by
  obtain ⟨i, b, hb, he⟩ := everyKey7_in_atlas k hk
  refine ⟨i, IndexedData7.owned_checked i, exposed7 i, ?_⟩
  rw [← he]
  exact BoxKey.keySolid_subset_collar supportValid7.1 (supportValid7.2.1 i b hb)

/-- Around every point of a key's support, all other exact keys are absent. -/
theorem T7_key_isolated {k : KeyData 7} (hk : k ∈ keys7)
    {p : Point 7} (hp : p ∈ keyCoordinateSupport k) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ keys7, j ≠ k → x ∉ keySolid j :=
  IndexedGeometry.key_isolation supportValid7 IndexedData7.facet_injective
    IndexedData7.owned_checked exposed7 everyKey7_in_atlas hk hp

/-- The actual body's germ is an exposed halfspace with exactly this signed key.
For dents the final closure is essential and remains in the conclusion. -/
theorem T7_isolated_key_halfspace {k : KeyData 7} (hk : k ∈ keys7)
    {p : Point 7} (hp : p ∈ keyCoordinateSupport k) :
    ∃ i : Fin 896, LocalSetEq p T7
      (closure (keyReplacement (IndexedData7.geometry.facet i).inwardHalfspace
        (keySolid k) k.bump)) :=
  IndexedGeometry.localSetEq_body_isolated_halfspace supportValid7
    IndexedData7.facet_injective IndexedData7.owned_checked exposed7
    everyKey7_in_atlas hk hp

/-- Every point has one of the two exact local material models. -/
theorem T7_local_body_inventory (p : Point 7) :
    LocalSetEq p T7 (carrier 7) ∨
      ∃ k ∈ keys7, ∃ i : Fin 896, LocalSetEq p T7
        (closure (keyReplacement (IndexedData7.geometry.facet i).inwardHalfspace
          (keySolid k) k.bump)) :=
  IndexedGeometry.localSetEq_body_inventory supportValid7
    IndexedData7.facet_injective IndexedData7.owned_checked exposed7
    everyKey7_in_atlas p

/-- The corresponding complete support-level boundary inventory. -/
theorem T7_local_boundary_inventory (p : Point 7) :
    LocalSetEq p (frontier T7) (frontier (carrier 7)) ∨
      ∃ k ∈ keys7, ∃ i : Fin 896, LocalSetEq p (frontier T7)
        (frontier (closure
          (keyReplacement (IndexedData7.geometry.facet i).inwardHalfspace
            (keySolid k) k.bump))) :=
  IndexedGeometry.localSetEq_frontier_body_inventory supportValid7
    IndexedData7.facet_injective IndexedData7.owned_checked exposed7
    everyKey7_in_atlas p

#print axioms T7_local_body_inventory
#print axioms T7_local_boundary_inventory

#print axioms T7_keySupports_disjoint
#print axioms T7_keySolids_disjoint
#print axioms T7_key_has_exposed_collar
#print axioms T7_key_isolated
#print axioms T7_isolated_key_halfspace

end SparseMonotiles
