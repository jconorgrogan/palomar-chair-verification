module

public import SpectreGeometry.PhysicalCornerConstraint
public import SpectreGeometry.SectorPartitionConsequences

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem physical_vertex_edge_star {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1)
    (x : EPlane)
    (hxe : x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f i (euclideanVertex j)) :
    ∃ (hr : x ∈ f root '' euclideanBody) (hi : x ∈ f i '' euclideanBody)
      (k : TileAt f x → Fin 12) (b : TileAt f x → BoundarySlot),
      k ⟨root,hr⟩ = 0 ∧ b ⟨root,hr⟩ = .inr e ∧ b ⟨i,hi⟩ = .inl j ∧
      (∀ a, BoundarySlotAt (b a) (sourcePoint (f a.val) x)) ∧
      (∀ a q, coordinateAction (f a.val) q = coordinateAction (f root) (rotate (k a) q)) ∧
      (∀ d : Fin 12, ∃! a : TileAt f x,
        slotSector (b a) (directionAdd (directionInverse (k a)) d)) := by
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
  exact ⟨hroot,hi,k,b,hk0,by simp [b],by simp [b,hij],hb,hk,hpart⟩

theorem sector_partition_other_slots_corners {ι : Type*}
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpartition : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d))
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (hroot : b root = .inr e) (hi : b i = .inl j) :
    ∀ a, a ≠ root → ∃ q, b a = .inl q := by
  classical
  intro a ha
  cases he : b a with
  | inl q => exact ⟨q,rfl⟩
  | inr q =>
      have hr6 : (slotSectorList (b root)).length = 6 := by
        rw [hroot]
        exact edge_sector_count e
      have ha6 : (slotSectorList (b a)).length = 6 := by
        rw [he]
        exact edge_sector_count q
      have hh := sector_partition_two_sixes k b hpartition root a (Ne.symm ha) hr6 ha6 i
      rcases hh with hh | hh
      · exact False.elim (hij hh)
      · have hbad := hi
        rw [hh,he] at hbad
        cases hbad

end
end SpectreGeometry
