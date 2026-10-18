module

public import SpectreGeometry.BoundarySectorGerms
public import SpectreGeometry.SectorRotations

@[expose] public section


/-! The literal boundary sector masks transported to arbitrary physical
placements using the proved twelve-relative-frame theorem. -/
namespace SpectreGeometry
noncomputable section
open Set

def sourcePoint (f : EPlane ≃ᵢ EPlane) (x : EPlane) : RealPoint :=
  euclideanCoordinates.symm (f.symm x)

theorem homeomorph_mem_image_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) (S : Set X) (y : Y) : y ∈ H '' S ↔ H.symm y ∈ S := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa using hx
  · intro h
    exact ⟨H.symm y,h,H.apply_symm_apply y⟩

theorem placed_body_mem_iff (f : EPlane ≃ᵢ EPlane) (y : EPlane) :
    y ∈ f '' euclideanBody ↔ sourcePoint f y ∈ polygonBody := by
  let H : RealPoint ≃ₜ EPlane := euclideanCoordinates.trans f.toHomeomorph
  have he : f '' euclideanBody = H '' polygonBody := by
    rw [euclideanBody,Set.image_image]
    rfl
  rw [he,homeomorph_mem_image_iff]
  rfl

theorem placed_interior_mem_iff (f : EPlane ≃ᵢ EPlane) (y : EPlane) :
    y ∈ interior (f '' euclideanBody) ↔ sourcePoint f y ∈ interior polygonBody := by
  let H : RealPoint ≃ₜ EPlane := euclideanCoordinates.trans f.toHomeomorph
  have he : f '' euclideanBody = H '' polygonBody := by
    rw [euclideanBody,Set.image_image]
    rfl
  rw [he,←H.image_interior,homeomorph_mem_image_iff]
  rfl

theorem placed_frontier_mem_iff (f : EPlane ≃ᵢ EPlane) (y : EPlane) :
    y ∈ frontier (f '' euclideanBody) ↔ sourcePoint f y ∈ frontier polygonBody := by
  let H : RealPoint ≃ₜ EPlane := euclideanCoordinates.trans f.toHomeomorph
  have he : f '' euclideanBody = H '' polygonBody := by
    rw [euclideanBody,Set.image_image]
    rfl
  rw [he,←H.image_frontier,homeomorph_mem_image_iff]
  rfl

/-- The rotated finite mask exactly characterizes actual small-ray body
and interior membership in the supplied physical copy. -/
theorem placed_boundary_slot_germ (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (x : EPlane) (b : BoundarySlot) (hb : BoundarySlotAt b (sourcePoint f x)) (d : Fin 12) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (framedRay root x d t ∈ f '' euclideanBody ↔ slotSector b (directionAdd (directionInverse k) d)) ∧
      (framedRay root x d t ∈ interior (f '' euclideanBody) ↔ slotSector b (directionAdd (directionInverse k) d)) := by
  obtain ⟨δ,hδ,hh⟩ := boundary_slot_actual_germ b (sourcePoint f x) hb
    (directionAdd (directionInverse k) d)
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ
  have he := relative_preimage_ray root f k hframe x d t
  change sourcePoint f (framedRay root x d t) = sourceRay (sourcePoint f x)
    (directionAdd (directionInverse k) d) t at he
  rw [placed_body_mem_iff,placed_interior_mem_iff,he]
  exact hh t ht htδ

theorem placed_frontier_has_sector_germ (root f : EPlane ≃ᵢ EPlane)
    (hrelated : CyclicFrameRelated root f) (x : EPlane) (hx : x ∈ frontier (f '' euclideanBody)) :
    ∃ (k : Fin 12) (b : BoundarySlot), BoundarySlotAt b (sourcePoint f x) ∧
      ∀ d : Fin 12, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
        (framedRay root x d t ∈ f '' euclideanBody ↔ slotSector b (directionAdd (directionInverse k) d)) ∧
        (framedRay root x d t ∈ interior (f '' euclideanBody) ↔ slotSector b (directionAdd (directionInverse k) d)) := by
  obtain ⟨k,hk⟩ := hrelated
  obtain ⟨b,hb⟩ := frontier_has_slot (sourcePoint f x) ((placed_frontier_mem_iff f x).1 hx)
  exact ⟨k,b,hb,fun d => placed_boundary_slot_germ root f k hk x b hb d⟩

/-- A genuine homochiral physical tiling supplies every relative-frame
hypothesis used in the local sector classification. -/
theorem homochiral_tiling_boundary_sector_germ {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root i : ι)
    (x : EPlane) (hx : x ∈ frontier (f i '' euclideanBody)) :
    ∃ (k : Fin 12) (b : BoundarySlot), BoundarySlotAt b (sourcePoint (f i) x) ∧
      ∀ d : Fin 12, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
        (framedRay (f root) x d t ∈ f i '' euclideanBody ↔ slotSector b (directionAdd (directionInverse k) d)) ∧
        (framedRay (f root) x d t ∈ interior (f i '' euclideanBody) ↔ slotSector b (directionAdd (directionInverse k) d)) :=
  placed_frontier_has_sector_germ (f root) (f i)
    (homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i) x hx

end
end SpectreGeometry
