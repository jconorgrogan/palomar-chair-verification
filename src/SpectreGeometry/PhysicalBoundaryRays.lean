module

public import SpectreGeometry.SectorPartitionRays

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem placed_edge_interpolate (f : EPlane ≃ᵢ EPlane) (e : Fin 14) (t : ℝ) :
    f (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)) =
      f (euclideanVertex e) + t • placedEdgeVector f e := by
  have hh : f (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)) -
      f (euclideanVertex e) = t • placedEdgeVector f e := by
    apply displacementPullback_injective f
    rw [displacementPullback_sub,f.symm_apply_apply,f.symm_apply_apply,
      euclideanCoordinates.symm_apply_apply,map_smul,displacementPullback_edge]
    change interpolate (realVertex e) (realVertex (next e)) t - realVertex e = t • realEdge e
    apply Prod.ext <;> simp only [interpolate,realEdge,RealPoint.sub,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  exact (eq_add_of_sub_eq hh).trans (add_comm _ _)

theorem relative_edge_opposite (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q, coordinateAction f q = coordinateAction root (rotate k q))
    (e j : Fin 14) (ht : directionAdd k (edgeTurn j) = directionAdd (edgeTurn e) 6) :
    placedEdgeVector f j = -placedEdgeVector root e := by
  apply coordinateLinearEquiv.symm.injective
  change euclideanCoordinates.symm (placedEdgeVector f j) =
    coordinateLinearEquiv.symm (-placedEdgeVector root e)
  rw [map_neg]
  change euclideanCoordinates.symm (placedEdgeVector f j) = -euclideanCoordinates.symm (placedEdgeVector root e)
  rw [←coordinateAction_edge,←coordinateAction_edge,hframe,real_edge_direction]
  change coordinateAction root (complexMulReal (realDirection k) (realDirection (edgeTurn j))) =
    -coordinateAction root (realEdge e)
  rw [realDirection_multiply,ht,realDirection_opposite,map_neg,←real_edge_direction]

theorem slot_corner_placed_point (f : EPlane ≃ᵢ EPlane) (x : EPlane) (q : Fin 14)
    (h : BoundarySlotAt (.inl q) (sourcePoint f x)) : x = f (euclideanVertex q) := by
  change sourcePoint f x = realVertex q at h
  have hh := congrArg (fun p => f (euclideanCoordinates p)) h
  simpa [sourcePoint,euclideanVertex] using hh

theorem physical_vertex_edge_boundary_rays {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1)
    (x : EPlane)
    (hxe : x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f i (euclideanVertex j)) :
    (∃ a q, a ≠ root ∧ x = f a (euclideanVertex q) ∧
      placedEdgeVector (f a) q = -placedEdgeVector (f root) e) ∧
    (∃ a q, a ≠ root ∧ x = f a (euclideanVertex q) ∧
      placedEdgeVector (f a) (previous q) = -placedEdgeVector (f root) e) := by
  classical
  obtain ⟨hr,hi,k,b,hk0,hbr,hbi,hb,hk,hpart⟩ :=
    physical_vertex_edge_star f hdirect hdisjoint hcover root i hij e j t ht ht' x hxe hxj
  have hne : (⟨i,hi⟩ : TileAt f x) ≠ ⟨root,hr⟩ := fun he => hij (congrArg Subtype.val he)
  have hcorn := sector_partition_other_slots_corners k b hpart ⟨root,hr⟩ ⟨i,hi⟩ hne e j hbr hbi
  obtain ⟨hl,hright⟩ := sector_partition_edge_rays k b hpart ⟨root,hr⟩ e hk0 hbr hcorn
  constructor
  · obtain ⟨a,q,ha,hq,hd⟩ := hl
    have hqa := hb a
    rw [hq] at hqa
    exact ⟨a.val,q,fun he => ha (Subtype.ext he),slot_corner_placed_point (f a.val) x q hqa,
      relative_edge_opposite (f root) (f a.val) (k a) (hk a) e q hd⟩
  · obtain ⟨a,q,ha,hq,hd⟩ := hright
    have hqa := hb a
    rw [hq] at hqa
    exact ⟨a.val,q,fun he => ha (Subtype.ext he),slot_corner_placed_point (f a.val) x q hqa,
      relative_edge_opposite (f root) (f a.val) (k a) (hk a) e (previous q) hd⟩

end
end SpectreGeometry
