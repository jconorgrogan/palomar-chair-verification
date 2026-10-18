module

public import SpectreGeometry.FiniteRayPartition

@[expose] public section


/-! Every actual boundary star in a genuine homochiral tiling determines a
partition of all twelve open direction sectors by its literal masks. Local
finiteness, all boundary germs, relative frames, coverage, and uniqueness are
derived; no sector partition is assumed. -/
namespace SpectreGeometry
noncomputable section
open Set

abbrev TileAt {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane) (x : EPlane) :=
  {i : ι // x ∈ f i '' euclideanBody}

theorem homochiral_physical_sector_partition {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root : ι) (x : EPlane) (hx : x ∈ frontier (f root '' euclideanBody)) :
    ∃ (k : TileAt f x → Fin 12) (b : TileAt f x → BoundarySlot),
      (∀ i, BoundarySlotAt (b i) (sourcePoint (f i.val) x)) ∧
      ∀ d : Fin 12, ∃! i : TileAt f x, slotSector (b i) (directionAdd (directionInverse (k i)) d) := by
  classical
  have hlocal := CompactPacking.polygon_packing_locallyFinite f hdisjoint
  letI : Fintype (TileAt f x) := (hlocal.point_finite x).fintype
  have hclosed : ∀ i, IsClosed (f i '' euclideanBody) :=
    fun i => (euclideanBody_compact.image (f i).continuous).isClosed
  have hregular : ∀ i, f i '' euclideanBody ⊆ closure (interior (f i '' euclideanBody)) := by
    intro i
    rw [placed_body_closure_interior]
  have hroot : x ∈ f root '' euclideanBody := (hclosed root).closure_subset hx.1
  have hfront : ∀ i : TileAt f x, x ∈ frontier (f i.val '' euclideanBody) := by
    intro i
    by_cases he : i.val = root
    · simpa only [he] using hx
    · exact (CompactTilingIncidence.common_point_frontiers (fun i => f i '' euclideanBody)
        hclosed hregular hdisjoint (Ne.symm he) hroot i.property).2
  choose k b hb hg using fun i : TileAt f x =>
    homochiral_tiling_boundary_sector_germ f hdirect hdisjoint hcover root i.val x (hfront i)
  refine ⟨k,b,hb,?_⟩
  apply finite_actual_ray_partition (fun i : TileAt f x => f i.val '' euclideanBody) (f root) x
    (fun i d => slotSector (b i) (directionAdd (directionInverse (k i)) d))
  · intro i j hij
    exact hdisjoint (fun he => hij (Subtype.ext he))
  · obtain ⟨r,hr,hstar⟩ := CompactTilingIncidence.local_star_radius (fun i => f i '' euclideanBody)
      hlocal hclosed x
    refine ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,?_⟩
    intro y hy
    obtain ⟨i,hi⟩ := hcover y
    exact ⟨⟨i,hstar i y hy hi⟩,hi⟩
  · exact hg

end
end SpectreGeometry
