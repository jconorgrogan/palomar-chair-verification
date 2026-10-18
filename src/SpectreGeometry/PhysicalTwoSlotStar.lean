module

public import SpectreGeometry.PrescribedSectorStar

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem boundary_slot_mem_frontier (b : BoundarySlot) (p : RealPoint)
    (h : BoundarySlotAt b p) : p ∈ frontier polygonBody := by
  cases b with
  | inl q =>
      change p = realVertex q at h
      rw [h]
      exact polygonEdge_subset_frontier q (vertex_mem_polygonEdge q)
  | inr q =>
      obtain ⟨t,ht,ht',rfl⟩ := h
      exact outer_open_edge_mem_frontier q t ht ht'

theorem physical_two_slot_star {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (x : EPlane)
    (bRoot bOther : BoundarySlot)
    (hxroot : BoundarySlotAt bRoot (sourcePoint (f root) x))
    (hxother : BoundarySlotAt bOther (sourcePoint (f i) x)) :
    ∃ (hr : x ∈ f root '' euclideanBody) (hi : x ∈ f i '' euclideanBody)
      (k : TileAt f x → Fin 12) (b : TileAt f x → BoundarySlot),
      k ⟨root,hr⟩ = 0 ∧ b ⟨root,hr⟩ = bRoot ∧ b ⟨i,hi⟩ = bOther ∧
      (∀ a, BoundarySlotAt (b a) (sourcePoint (f a.val) x)) ∧
      (∀ a q, coordinateAction (f a.val) q = coordinateAction (f root) (rotate (k a) q)) ∧
      (∀ d : Fin 12, ∃! a : TileAt f x,
        slotSector (b a) (directionAdd (directionInverse (k a)) d)) := by
  classical
  have hfrontroot : x ∈ frontier (f root '' euclideanBody) :=
    (placed_frontier_mem_iff (f root) x).2 (boundary_slot_mem_frontier bRoot _ hxroot)
  have hfrontother : x ∈ frontier (f i '' euclideanBody) :=
    (placed_frontier_mem_iff (f i) x).2 (boundary_slot_mem_frontier bOther _ hxother)
  have hclosed : ∀ a, IsClosed (f a '' euclideanBody) :=
    fun a => (euclideanBody_compact.image (f a).continuous).isClosed
  have hregular : ∀ a, f a '' euclideanBody ⊆ closure (interior (f a '' euclideanBody)) := by
    intro a
    rw [placed_body_closure_interior]
  have hroot : x ∈ f root '' euclideanBody := (hclosed root).closure_subset hfrontroot.1
  have hi : x ∈ f i '' euclideanBody := (hclosed i).closure_subset hfrontother.1
  have hfront : ∀ a : TileAt f x, x ∈ frontier (f a.val '' euclideanBody) := by
    intro a
    by_cases he : a.val = root
    · simpa only [he] using hfrontroot
    · exact (CompactTilingIncidence.common_point_frontiers (fun a => f a '' euclideanBody)
        hclosed hregular hdisjoint (Ne.symm he) hroot a.property).2
  choose b₀ hb₀ using fun a : TileAt f x =>
    frontier_has_slot (sourcePoint (f a.val) x) ((placed_frontier_mem_iff (f a.val) x).1 (hfront a))
  let b : TileAt f x → BoundarySlot := fun a =>
    if a.val = root then bRoot else if a.val = i then bOther else b₀ a
  have hb : ∀ a, BoundarySlotAt (b a) (sourcePoint (f a.val) x) := by
    intro a
    dsimp only [b]
    split_ifs with he he
    · simpa only [he] using hxroot
    · simpa only [he] using hxother
    · exact hb₀ a
  obtain ⟨k,hk0,hk,hpart⟩ := homochiral_sector_partition_of_slots f hdirect hdisjoint hcover root x hroot b hb
  exact ⟨hroot,hi,k,b,hk0,by simp [b],by simp [b,hij],hb,hk,hpart⟩

end
end SpectreGeometry
