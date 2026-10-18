module

public import SpectreGeometry.PhysicalSectorStar

@[expose] public section


/-! The physical sector star can retain prescribed actual boundary slots
and the actual relative frames needed for geometric ray transport. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem homochiral_sector_partition_of_slots {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root : ι) (x : EPlane) (hx : x ∈ f root '' euclideanBody)
    (b : TileAt f x → BoundarySlot)
    (hb : ∀ i, BoundarySlotAt (b i) (sourcePoint (f i.val) x)) :
    ∃ k : TileAt f x → Fin 12,
      k ⟨root,hx⟩ = 0 ∧
      (∀ i q, coordinateAction (f i.val) q = coordinateAction (f root) (rotate (k i) q)) ∧
      ∀ d : Fin 12, ∃! i : TileAt f x,
        slotSector (b i) (directionAdd (directionInverse (k i)) d) := by
  classical
  have hlocal := CompactPacking.polygon_packing_locallyFinite f hdisjoint
  letI : Fintype (TileAt f x) := (hlocal.point_finite x).fintype
  have hchoices : ∀ i : TileAt f x, ∃ k : Fin 12,
      (i.val = root → k = 0) ∧
      ∀ q, coordinateAction (f i.val) q = coordinateAction (f root) (rotate k q) := by
    intro i
    by_cases hi : i.val = root
    · exact ⟨0,fun _ => rfl,by intro q; rw [hi,rotate_zero]⟩
    · obtain ⟨k,hk⟩ := homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i.val
      exact ⟨k,fun he => False.elim (hi he),hk⟩
  choose k hk0 hk using hchoices
  refine ⟨k,hk0 ⟨root,hx⟩ rfl,hk,?_⟩
  apply finite_actual_ray_partition (fun i : TileAt f x => f i.val '' euclideanBody) (f root) x
    (fun i d => slotSector (b i) (directionAdd (directionInverse (k i)) d))
  · intro i j hij
    exact hdisjoint (fun he => hij (Subtype.ext he))
  · have hclosed : ∀ i, IsClosed (f i '' euclideanBody) :=
      fun i => (euclideanBody_compact.image (f i).continuous).isClosed
    obtain ⟨r,hr,hstar⟩ := CompactTilingIncidence.local_star_radius (fun i => f i '' euclideanBody)
      hlocal hclosed x
    refine ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,?_⟩
    intro y hy
    obtain ⟨i,hi⟩ := hcover y
    exact ⟨⟨i,hstar i y hy hi⟩,hi⟩
  · intro i d
    exact placed_boundary_slot_germ (f root) (f i.val) (k i) (hk i) x (b i) (hb i) d

end
end SpectreGeometry
