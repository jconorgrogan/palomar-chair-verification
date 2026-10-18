module

public import SpectreGeometry.DeformationHomeomorphismPhysical
public import SpectreGeometry.DeformationHomeomorphismBounds

@[expose] public section


/-! The physical deformation's actual carrier images, coverage, packing,
and noncollapse of physically realized vertex displacements. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

@[simp] theorem normalizedPhysicalHomeomorph_apply (x : EPlane) :
    normalizedPhysicalHomeomorph f hdirect hdisjoint hcover root x =
      normalizedPLMap f hdirect hdisjoint hcover root x := by
  simp only [normalizedPhysicalHomeomorph,homeomorphOfAffineCover_apply]

/-- The same homeomorphism in the original arbitrary physical coordinate frame. -/
def physicalHomeomorph : EPlane ≃ₜ EPlane :=
  (f root).symm.toHomeomorph.trans (normalizedPhysicalHomeomorph f hdirect hdisjoint hcover root)

theorem physicalHomeomorph_apply (x : EPlane) :
    physicalHomeomorph f hdirect hdisjoint hcover root x =
      euclideanCoordinates (physicalPastedMap f hcover
        (physicalTilePL f hdirect hdisjoint hcover root) x) := by
  change normalizedPhysicalHomeomorph f hdirect hdisjoint hcover root ((f root).symm x) = _
  rw [normalizedPhysicalHomeomorph_apply,normalizedPLMap,(f root).apply_symm_apply]

theorem physicalHomeomorph_on_tile (i : ι) (p : RealPoint) (hp : p ∈ polygonBody) :
    physicalHomeomorph f hdirect hdisjoint hcover root (f i (euclideanCoordinates p)) =
      euclideanCoordinates (tilingTargetOrigin f hdirect hdisjoint hcover root i+
        tilePLMap (tilingFrame f hdirect hdisjoint hcover root i) p) := by
  rw [physicalHomeomorph_apply,physicalPastedMap_on_tile f hdirect hdisjoint hcover
    (physicalVertexDevelopment (f root)) (physicalTilePL f hdirect hdisjoint hcover root)
    (physicalTilePL_boundary f hdirect hdisjoint hcover root) i _
    (show f i (euclideanCoordinates p) ∈ f i '' euclideanBody from
      ⟨euclideanCoordinates p,⟨p,hp,rfl⟩,rfl⟩)]
  simp only [physicalTilePL,sourcePoint,(f i).symm_apply_apply,euclideanCoordinates.symm_apply_apply]

def developedPlacedBody (i : ι) : Set EPlane :=
  (fun p => euclideanCoordinates (tilingTargetOrigin f hdirect hdisjoint hcover root i+p)) ''
    targetBody (tilingFrame f hdirect hdisjoint hcover root i)

theorem physicalHomeomorph_image_tile (i : ι) :
    physicalHomeomorph f hdirect hdisjoint hcover root '' (f i '' euclideanBody) =
      developedPlacedBody f hdirect hdisjoint hcover root i := by
  ext y
  constructor
  · rintro ⟨z,⟨u,⟨p,hp,rfl⟩,rfl⟩,rfl⟩
    refine ⟨tilePLMap (tilingFrame f hdirect hdisjoint hcover root i) p,?_,?_⟩
    · rw [←tilePLMap_image_body]
      exact ⟨p,hp,rfl⟩
    · exact (physicalHomeomorph_on_tile f hdirect hdisjoint hcover root i p hp).symm
  · rintro ⟨q,hq,rfl⟩
    rw [←tilePLMap_image_body] at hq
    obtain ⟨p,hp,hpq⟩ := hq
    refine ⟨f i (euclideanCoordinates p),⟨euclideanCoordinates p,⟨p,hp,rfl⟩,rfl⟩,?_⟩
    rw [physicalHomeomorph_on_tile f hdirect hdisjoint hcover root i p hp,hpq]

/-- The literal developed triangle carriers tile the entire Euclidean plane.
Only the ordinary original tiling assumptions occur as inputs. -/
theorem homochiral_developed_plane_tiling :
    (∀ x, ∃ i, x ∈ developedPlacedBody f hdirect hdisjoint hcover root i) ∧
      Pairwise (fun i j => Disjoint
        (interior (developedPlacedBody f hdirect hdisjoint hcover root i))
        (interior (developedPlacedBody f hdirect hdisjoint hcover root j))) :=
  tiling_transport (physicalHomeomorph f hdirect hdisjoint hcover root)
    (fun i => f i '' euclideanBody) (developedPlacedBody f hdirect hdisjoint hcover root)
    hcover hdisjoint (physicalHomeomorph_image_tile f hdirect hdisjoint hcover root)

theorem physicalHomeomorph_vertex (i : ι) (e : Fin 14) :
    physicalHomeomorph f hdirect hdisjoint hcover root (f i (euclideanVertex e)) =
      euclideanCoordinates (physicalVertexDevelopment (f root) (f i (euclideanVertex e))) := by
  have hp : realVertex e ∈ polygonBody :=
    mem_iUnion.mpr ⟨e,polygonEdge_mem_triangleBody e (vertex_mem_polygonEdge e)⟩
  rw [euclideanVertex,physicalHomeomorph_on_tile f hdirect hdisjoint hcover root i _ hp,tilePLMap_vertex]
  exact congrArg euclideanCoordinates
    (homochiral_vertex_development_formula f hdirect hdisjoint hcover root i _
      (tilingFrame_spec f hdirect hdisjoint hcover root i) e).symm

include hdirect hdisjoint hcover in
/-- Although the additive arithmetic development has a kernel, its restriction
to the vertices of any actual admissible tiling is injective. -/
theorem physically_realized_vertex_development_injective (i j : ι) (e v : Fin 14)
    (h : physicalVertexDevelopment (f root) (f i (euclideanVertex e)) =
      physicalVertexDevelopment (f root) (f j (euclideanVertex v))) :
    f i (euclideanVertex e) = f j (euclideanVertex v) := by
  apply (physicalHomeomorph f hdirect hdisjoint hcover root).injective
  rw [physicalHomeomorph_vertex,physicalHomeomorph_vertex,h]

end Tiling
end
end SpectreGeometry.Deformation
