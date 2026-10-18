module

public import SpectreGeometry.PhysicalGridPeriod
public import SpectreGeometry.QuadraticFrameUniqueness

@[expose] public section


/-! Source-correct ownership and root-change facts for the accepted physical
construction. This module does not assert the missing real/discrete contact
correspondence or the sparse-hat branch reduction. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreGeometry.Deformation

private theorem placementCells_has_cell (p : HTPlacement) : ∃ c, c ∈ placementCells p := by
  refine ⟨moveCell p.turn p.center ⟨(0,0),0⟩,List.mem_map.mpr ⟨⟨(0,0),0⟩,?_,rfl⟩⟩
  cases p.kind <;> decide

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

/-- Every owned extracted placement is the image of an actual original tile. -/
theorem physicalGridField_owned_source (p : HTPlacement)
    (hp : RootOwned (physicalGridField f hdirect hdisjoint hcover root) p) :
    ∃ i, tilingGridPlacement f hdirect hdisjoint hcover root i = p := by
  obtain ⟨c,hc⟩ := placementCells_has_cell p
  exact ⟨probeOwner (tilingGridPlacement f hdirect hdisjoint hcover root)
    (homochiral_literal_kite_tiling f hdirect hdisjoint hcover root).1 c,hp c hc⟩

/-- Two original indices cannot yield the same literal placement: a shared
cell probe would lie in both ordinary interiors. -/
theorem tilingGridPlacement_injective :
    Function.Injective (tilingGridPlacement f hdirect hdisjoint hcover root) := by
  intro i j hij
  by_contra hne
  obtain ⟨c,hc⟩ := placementCells_has_cell (tilingGridPlacement f hdirect hdisjoint hcover root i)
  have hi := gridProbe_interior_placement _ c hc
  have hj := gridProbe_interior_placement _ c (hij ▸ hc)
  exact Set.disjoint_left.mp
    ((homochiral_literal_kite_tiling f hdirect hdisjoint hcover root).2 hne) hi hj

/-- A source-correct equivalence, retaining the identity of every original tile. -/
def physicalTileOccurrenceEquiv :
    ι ≃ {p : HTPlacement // RootOwned (physicalGridField f hdirect hdisjoint hcover root) p} :=
  Equiv.ofBijective
    (fun i => ⟨tilingGridPlacement f hdirect hdisjoint hcover root i,
      physicalGridField_owns f hdirect hdisjoint hcover root i⟩)
    ⟨fun i j h => tilingGridPlacement_injective f hdirect hdisjoint hcover root
        (congrArg Subtype.val h),
      fun p => by
        obtain ⟨i,hi⟩ := physicalGridField_owned_source f hdirect hdisjoint hcover root p.val p.property
        exact ⟨i,Subtype.ext hi⟩⟩

@[simp] theorem physicalTileOccurrenceEquiv_val (i : ι) :
    (physicalTileOccurrenceEquiv f hdirect hdisjoint hcover root i).val =
      tilingGridPlacement f hdirect hdisjoint hcover root i := rfl

/-- Exact old-frame/new-frame composition, without making any choices consistent
by fiat. Uniqueness of the actual relative cyclic rotations forces the law. -/
theorem tilingFrame_root_change_add (newroot i : ι) :
    tilingFrame f hdirect hdisjoint hcover root i =
      directionAdd (tilingFrame f hdirect hdisjoint hcover root newroot)
        (tilingFrame f hdirect hdisjoint hcover newroot i) :=
  relative_frames_compose (f root) (f newroot) (f i) _ _ _
    (tilingFrame_spec f hdirect hdisjoint hcover root newroot)
    (tilingFrame_spec f hdirect hdisjoint hcover root i)
    (tilingFrame_spec f hdirect hdisjoint hcover newroot i)

/-- The corresponding modulo-twelve subtraction formula. -/
theorem tilingFrame_root_change (newroot i : ι) :
    tilingFrame f hdirect hdisjoint hcover newroot i =
      directionAdd (directionInverse (tilingFrame f hdirect hdisjoint hcover root newroot))
        (tilingFrame f hdirect hdisjoint hcover root i) := by
  rw [tilingFrame_root_change_add f hdirect hdisjoint hcover root newroot i,
    ←direction_add_assoc,direction_inverse_left]
  have hzero : ∀ a : Fin 12, directionAdd 0 a = a := by decide
  rw [hzero]

/-- Changing the root changes plane coordinates through an actual homeomorphism. -/
def rootChangeGridHomeomorph (newroot : ι) : RealPoint ≃ₜ RealPoint :=
  (physicalToGridHomeomorph f hdirect hdisjoint hcover root).symm.trans
    (physicalToGridHomeomorph f hdirect hdisjoint hcover newroot)

/-- It maps every old-root closed tile carrier onto the new-root carrier of
exactly the same original tile. -/
theorem rootChangeGridHomeomorph_image_tile (newroot i : ι) :
    rootChangeGridHomeomorph f hdirect hdisjoint hcover root newroot ''
      placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i) =
    placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover newroot i) := by
  rw [←physicalToGridHomeomorph_image_tile f hdirect hdisjoint hcover root i]
  change (fun x => physicalToGridHomeomorph f hdirect hdisjoint hcover newroot
    ((physicalToGridHomeomorph f hdirect hdisjoint hcover root).symm x)) '' _ = _
  rw [←Set.image_image]
  have hcancel : (physicalToGridHomeomorph f hdirect hdisjoint hcover root).symm ''
      (physicalToGridHomeomorph f hdirect hdisjoint hcover root) '' (f i '' euclideanBody) =
      f i '' euclideanBody :=
    (physicalToGridHomeomorph f hdirect hdisjoint hcover root).symm_image_image _
  rw [hcancel,physicalToGridHomeomorph_image_tile]

end Tiling
end
end SpectreGeometry
