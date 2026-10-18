module

public import SpectreGeometry.WholeEdgeRegistration
public import SpectreGeometry.EdgeMaskAlignmentData

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem packing_relative_edge_opposite (root f : EPlane ≃ᵢ EPlane)
    (hdisjoint : Disjoint (interior (root '' euclideanBody)) (interior (f '' euclideanBody)))
    (k : Fin 12) (hframe : ∀ q, coordinateAction f q = coordinateAction root (rotate k q))
    (e j : Fin 14) (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hxe : x = root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u))) :
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn e) 6 := by
  apply disjoint_edge_masks_opposite e j k
  intro d hd hj
  have he : BoundarySlotAt (.inr e) (sourcePoint root x) := by
    rw [hxe,sourcePoint_image]
    exact ⟨t,ht,ht',rfl⟩
  have hf : BoundarySlotAt (.inr j) (sourcePoint f x) := by
    rw [hxj,sourcePoint_image]
    exact ⟨u,hu,hu',rfl⟩
  obtain ⟨δ,hδ,hgr⟩ := placed_boundary_slot_germ root root 0
    (by intro q; rw [rotate_zero]) x (.inr e) he d
  obtain ⟨ε,hε,hgf⟩ := placed_boundary_slot_germ root f k hframe x (.inr j) hf d
  let s := min δ ε / 2
  have hs : 0 < s := div_pos (lt_min hδ hε) (by norm_num)
  have hsδ : s < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hε)) (min_le_left _ _)
  have hsε : s < ε := lt_of_lt_of_le (half_lt_self (lt_min hδ hε)) (min_le_right _ _)
  have hd' : slotSector (.inr e) (directionAdd (directionInverse 0) d) := by
    change edgeSector e (directionAdd 0 d)
    rwa [direction_zero_add]
  exact Set.disjoint_left.mp hdisjoint ((hgr s hs hsδ).2.2 hd') ((hgf s hs hsε).2.2 hj)

theorem homochiral_contact_unit_edges_reversed {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hxe : x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f i (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u))) :
    f root (euclideanVertex e) = f i (euclideanVertex (next j)) ∧
    f root (euclideanVertex (next e)) = f i (euclideanVertex j) := by
  obtain ⟨k,hk⟩ := homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i
  have ho := packing_relative_edge_opposite (f root) (f i) (hdisjoint (Ne.symm hij))
    k hk e j t u ht ht' hu hu' x hxe hxj
  have hn := relative_edge_opposite (f root) (f i) k hk e j ho
  rcases homochiral_contact_unit_edges_whole f hdirect hdisjoint hcover root i hij e j
      t u ht ht' hu hu' x hxe hxj with ⟨ha,hb⟩ | h
  · have hv : placedEdgeVector (f root) e = -placedEdgeVector (f root) e := by
      simpa only [placedEdgeVector,←ha,←hb] using hn
    have hz : placedEdgeVector (f root) e = 0 := by
      ext n
      change (placedEdgeVector (f root) e) n = 0
      have hh := congrArg (fun v : EPlane => v n) hv
      change (placedEdgeVector (f root) e) n = -(placedEdgeVector (f root) e) n at hh
      linarith
    have hu := placedEdgeVector_unit (f root) e
    rw [hz,norm_zero] at hu
    norm_num at hu
  · exact h

end
end SpectreGeometry
