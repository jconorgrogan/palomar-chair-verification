module

public import SpectreGeometry.PhysicalGridRootParity
public import SpectreGeometry.GridKiteContactReal
public import SpectreClusters.SwappedSparsePhase

@[expose] public section


/-! The alternate sparse phase uses the same original physical tiles, with
an actual root change and a proved closed-carrier/contact correspondence. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.DeformedLiteralBinding SpectreGeometry.Deformation

private theorem homeomorph_inter_nonempty_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (H : X ≃ₜ Y) (A B : Set X) :
    (H '' A ∩ H '' B).Nonempty ↔ (A ∩ B).Nonempty := by
  constructor
  · rintro ⟨z,⟨x,hx,rfl⟩,⟨y,hy,he⟩⟩
    have hyx : y=x := H.injective he
    exact ⟨x,hx,hyx ▸ hy⟩
  · rintro ⟨x,hx,hy⟩
    exact ⟨H x,⟨x,hx,rfl⟩,⟨x,hy,rfl⟩⟩

variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

theorem tilingGridPlacement_root_change_contact (newroot i j : ι) :
    ShapeContact (placementCells (tilingGridPlacement f hdirect hdisjoint hcover newroot i))
      (placementCells (tilingGridPlacement f hdirect hdisjoint hcover newroot j)) ↔
    ShapeContact (placementCells (tilingGridPlacement f hdirect hdisjoint hcover root i))
      (placementCells (tilingGridPlacement f hdirect hdisjoint hcover root j)) := by
  rw [shapeContact_iff_placementKiteBody_inter,shapeContact_iff_placementKiteBody_inter,
    ←rootChangeGridHomeomorph_image_tile f hdirect hdisjoint hcover root newroot i,
    ←rootChangeGridHomeomorph_image_tile f hdirect hdisjoint hcover root newroot j]
  exact homeomorph_inter_nonempty_iff _ _ _

def rootChangeOccurrenceEquiv (newroot : ι) :
    OwnedTile (physicalGridField f hdirect hdisjoint hcover root) ≃
    OwnedTile (physicalGridField f hdirect hdisjoint hcover newroot) :=
  (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover root).symm.trans
    (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover newroot)

@[simp] theorem rootChangeOccurrenceEquiv_source (newroot i : ι) :
    rootChangeOccurrenceEquiv f hdirect hdisjoint hcover root newroot
      (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover root i) =
    physicalTileOccurrenceEquiv f hdirect hdisjoint hcover newroot i := by
  simp [rootChangeOccurrenceEquiv]

theorem tilingGridPlacement_root_change_neighbor (newroot i j : ι) :
    StageA.FieldNeighbor (physicalGridField f hdirect hdisjoint hcover newroot)
      (tilingGridPlacement f hdirect hdisjoint hcover newroot i)
      (tilingGridPlacement f hdirect hdisjoint hcover newroot j) ↔
    StageA.FieldNeighbor (physicalGridField f hdirect hdisjoint hcover root)
      (tilingGridPlacement f hdirect hdisjoint hcover root i)
      (tilingGridPlacement f hdirect hdisjoint hcover root j) := by
  have he (r : ι) : tilingGridPlacement f hdirect hdisjoint hcover r j =
      tilingGridPlacement f hdirect hdisjoint hcover r i ↔ j=i :=
    (tilingGridPlacement_injective f hdirect hdisjoint hcover r).eq_iff
  simp only [StageA.FieldNeighbor,physicalGridField_owns,true_and,ne_eq,he,
    tilingGridPlacement_root_change_contact f hdirect hdisjoint hcover root newroot i j]

/-- Genuine source-correct swapped correspondence, not a relabeling of poses. -/
def physicalRootSwappedCorrespondence (newroot : ι)
    (hhat : (tilingGridPlacement f hdirect hdisjoint hcover root newroot).kind = .hat) :
    SwappedFieldCorrespondence (physicalGridField f hdirect hdisjoint hcover root)
      (physicalGridField f hdirect hdisjoint hcover newroot) where
  occurrences := rootChangeOccurrenceEquiv f hdirect hdisjoint hcover root newroot
  inverse := (rootChangeOccurrenceEquiv f hdirect hdisjoint hcover root newroot).symm
  inverse_occurrences := (rootChangeOccurrenceEquiv f hdirect hdisjoint hcover root newroot).symm_apply_apply
  occurrences_inverse := (rootChangeOccurrenceEquiv f hdirect hdisjoint hcover root newroot).apply_symm_apply
  kind_flip := by
    intro p
    obtain ⟨i,rfl⟩ := (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover root).surjective p
    rw [rootChangeOccurrenceEquiv_source,physicalTileOccurrenceEquiv_val,physicalTileOccurrenceEquiv_val]
    exact tilingGridPlacement_root_change_kind f hdirect hdisjoint hcover root newroot i hhat
  neighbor_iff := by
    intro p q
    obtain ⟨i,rfl⟩ := (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover root).surjective p
    obtain ⟨j,rfl⟩ := (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover root).surjective q
    simp only [rootChangeOccurrenceEquiv_source,physicalTileOccurrenceEquiv_val]
    exact tilingGridPlacement_root_change_neighbor f hdirect hdisjoint hcover root newroot i j

include root in
/-- One actual source root always realizes the turtle-sparse phase, conditional
only on the finite capture endpoint still supplied explicitly. -/
theorem exists_root_sparseTurtles (hcaptures : StageA.FinalCaptures) :
    ∃ r : ι, StageA.SparseTurtles (physicalGridField f hdirect hdisjoint hcover r) := by
  obtain ⟨newroot,hhat⟩ := exists_hat_source f hdirect hdisjoint hcover root hcaptures
  rcases StageA.one_of_swapped_fields_sparse hcaptures _ _
    (physicalGridField_valid f hdirect hdisjoint hcover root)
    (physicalRootSwappedCorrespondence f hdirect hdisjoint hcover root newroot hhat) with h | h
  · exact ⟨root,h⟩
  · exact ⟨newroot,h⟩

include hdirect hdisjoint hcover root in
/-- A nonzero physical period remains a nonzero grid period for whichever
actual root gives the turtle-sparse field. -/
theorem physical_period_has_sparse_periodic_grid (hcaptures : StageA.FinalCaptures)
    (v : EPlane) (hv : v ≠ 0) (hperiod : CarrierCollectionPeriod f v) :
    ∃ g : Cell → HTPlacement, ValidGridField g ∧ StageA.SparseTurtles g ∧
      ∃ u : SpectreClusters.Point, u ≠ 0 ∧ GridFieldTranslationPeriod g u := by
  obtain ⟨r,hr⟩ := exists_root_sparseTurtles f hdirect hdisjoint hcover root hcaptures
  exact ⟨physicalGridField f hdirect hdisjoint hcover r,
    physicalGridField_valid f hdirect hdisjoint hcover r,hr,
    physical_collection_period_to_grid_period f hdirect hdisjoint hcover r v hv hperiod⟩

end
end SpectreGeometry
