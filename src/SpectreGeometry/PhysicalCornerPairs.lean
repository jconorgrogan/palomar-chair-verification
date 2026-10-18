module

public import SpectreGeometry.PhysicalTwoSlotStar
public import SpectreGeometry.PhysicalCornerConstraint
public import SpectreGeometry.CornerPairSums
public import SpectreGeometry.DeformedVertexData

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem physical_corner_contact_allowed {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (heq : f root (euclideanVertex e) = f i (euclideanVertex j)) :
    AllowedCornerPair e j := by
  classical
  let x := f root (euclideanVertex e)
  have hxroot : BoundarySlotAt (.inl e) (sourcePoint (f root) x) :=
    sourcePoint_image (f root) (realVertex e)
  have hxother : BoundarySlotAt (.inl j) (sourcePoint (f i) x) := by
    change sourcePoint (f i) (f root (euclideanVertex e)) = realVertex j
    rw [heq]
    exact sourcePoint_image (f i) (realVertex j)
  obtain ⟨hr,hi,k,b,hk0,hbr,hbi,hb,hk,hpart⟩ :=
    physical_two_slot_star f hdirect hdisjoint hcover root i hij x (.inl e) (.inl j) hxroot hxother
  have hlocal := CompactPacking.polygon_packing_locallyFinite f hdisjoint
  letI : Fintype (TileAt f x) := (hlocal.point_finite x).fintype
  have hh := sector_partition_pair_sum k b hpart ⟨root,hr⟩ ⟨i,hi⟩
    (fun he => hij (congrArg Subtype.val he).symm)
  rw [hbr,hbi] at hh
  change (cornerSectorList e).length + (cornerSectorList j).length = 6 ∨
    (cornerSectorList e).length + (cornerSectorList j).length = 8 ∨
    (cornerSectorList e).length + (cornerSectorList j).length = 9 ∨
    (cornerSectorList e).length + (cornerSectorList j).length = 12 at hh
  simpa only [AllowedCornerPair,corner_sector_count] using hh

theorem physical_reversed_edge_pair_allowed {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (hleft : f root (euclideanVertex e) = f i (euclideanVertex (next j)))
    (hright : f root (euclideanVertex (next e)) = f i (euclideanVertex j)) :
    AllowedReversedEdgePair e j :=
  ⟨physical_corner_contact_allowed f hdirect hdisjoint hcover root i hij e (next j) hleft,
    physical_corner_contact_allowed f hdirect hdisjoint hcover root i hij (next e) j hright⟩

end
end SpectreGeometry
