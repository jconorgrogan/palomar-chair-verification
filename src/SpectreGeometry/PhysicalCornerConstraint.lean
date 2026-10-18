module

public import SpectreGeometry.PrescribedSectorStar
public import SpectreGeometry.SectorPartitionCounts

@[expose] public section


/-! Actual vertices lying in another tile's strict unit edge can only have
three or six thirty-degree sectors. This is derived from a physical tiling. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem sourcePoint_image (f : EPlane ≃ᵢ EPlane) (p : RealPoint) :
    sourcePoint f (f (euclideanCoordinates p)) = p := by
  simp [sourcePoint]

theorem physical_vertex_in_edge_corner_constraint {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1)
    (x : EPlane)
    (hxe : x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f i (euclideanVertex j)) :
    cornerSteps j = 3 ∨ cornerSteps j = 6 := by
  classical
  have hfrontroot : x ∈ frontier (f root '' euclideanBody) := by
    apply (placed_frontier_mem_iff (f root) x).2
    rw [hxe,sourcePoint_image]
    exact outer_open_edge_mem_frontier e t ht ht'
  have hclosed : ∀ a, IsClosed (f a '' euclideanBody) :=
    fun a => (euclideanBody_compact.image (f a).continuous).isClosed
  have hregular : ∀ a, f a '' euclideanBody ⊆ closure (interior (f a '' euclideanBody)) := by
    intro a
    rw [placed_body_closure_interior]
  have hroot : x ∈ f root '' euclideanBody := (hclosed root).closure_subset hfrontroot.1
  have hi : x ∈ f i '' euclideanBody := by
    apply (placed_body_mem_iff (f i) x).2
    rw [hxj]
    change sourcePoint (f i) (f i (euclideanCoordinates (realVertex j))) ∈ polygonBody
    rw [sourcePoint_image]
    exact (polygonBody_compact.isClosed).closure_subset
      (polygonEdge_subset_frontier j (vertex_mem_polygonEdge j)).1
  have hfront : ∀ a : TileAt f x, x ∈ frontier (f a.val '' euclideanBody) := by
    intro a
    by_cases he : a.val = root
    · simpa only [he] using hfrontroot
    · exact (CompactTilingIncidence.common_point_frontiers (fun a => f a '' euclideanBody)
        hclosed hregular hdisjoint (Ne.symm he) hroot a.property).2
  choose b₀ hb₀ using fun a : TileAt f x =>
    frontier_has_slot (sourcePoint (f a.val) x) ((placed_frontier_mem_iff (f a.val) x).1 (hfront a))
  let b : TileAt f x → BoundarySlot := fun a =>
    if a.val = root then .inr e else if a.val = i then .inl j else b₀ a
  have hb : ∀ a, BoundarySlotAt (b a) (sourcePoint (f a.val) x) := by
    intro a
    dsimp only [b]
    split_ifs with he he
    · rw [he,hxe,sourcePoint_image]
      exact ⟨t,ht,ht',rfl⟩
    · change sourcePoint (f a.val) x = realVertex j
      rw [he,hxj]
      exact sourcePoint_image (f i) (realVertex j)
    · exact hb₀ a
  obtain ⟨k,hk0,hk,hpart⟩ := homochiral_sector_partition_of_slots f hdirect hdisjoint hcover root x hroot b hb
  have hlocal := CompactPacking.polygon_packing_locallyFinite f hdisjoint
  letI : Fintype (TileAt f x) := (hlocal.point_finite x).fintype
  have hbroot : (slotSectorList (b ⟨root,hroot⟩)).length = 6 := by
    simp only [b,↓reduceIte]
    exact edge_sector_count e
  have hbother := sector_partition_other_size k b hpart ⟨root,hroot⟩ hbroot ⟨i,hi⟩
    (fun he => hij (congrArg Subtype.val he))
  have hbi : b ⟨i,hi⟩ = .inl j := by simp [b,hij]
  rw [hbi] at hbother
  change (cornerSectorList j).length = 3 ∨ (cornerSectorList j).length = 6 at hbother
  rwa [corner_sector_count] at hbother

end
end SpectreGeometry
