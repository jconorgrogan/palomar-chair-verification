module

public import SpectreGeometry.BoundarySectorGerms
public import SpectreGeometry.LocalConeGerm

@[expose] public section


/-! Literal all-direction polygon cone germs. These extend local body formulas,
not sample-ray tests, and do not assert an angular-measure formula. -/
namespace SpectreGeometry
noncomputable section
open Set

/-- The two incident wedges, retaining the actual radial separator. -/
def polygonVertexCone (i : Fin 14) : Set RealPoint :=
  {v | (0 ≤ RealPoint.det (realEdge (previous i)) v ∧
      RealPoint.det (RealPoint.sub (realVertex i) realFanCenter) v ≤ 0) ∨
    (0 ≤ RealPoint.det (RealPoint.sub (realVertex i) realFanCenter) v ∧
      0 ≤ RealPoint.det (realEdge i) v)}

def polygonBoundaryCone (b : BoundarySlot) : Set RealPoint :=
  match b with
  | .inl i => polygonVertexCone i
  | .inr i => {v | 0 ≤ RealPoint.det (realEdge i) v}

private theorem side_add_vector (a b x v : RealPoint) :
    side a b (x+v) = side a b x + RealPoint.det (RealPoint.sub b a) v := by
  simpa only [one_smul, one_mul] using side_add_ray a b x v 1

theorem cornerBodyCondition_add_vector (i : Fin 14) (v : RealPoint) :
    cornerBodyCondition i (realVertex i+v) ↔ v ∈ polygonVertexCone i := by
  have hp : RealPoint.sub (realVertex i) (realVertex (previous i)) =
      realEdge (previous i) := by simp only [realEdge, next_previous]
  simp only [cornerBodyCondition, radialSide, side_add_vector, side_self_right,
    side_self_left, zero_add, hp, polygonVertexCone, Set.mem_setOf_eq, realEdge]

theorem polygon_vertex_local_cone (i : Fin 14) :
    LocalConeGerm polygonBody (realVertex i) (polygonVertexCone i) := by
  obtain ⟨U,hU,hx,hbody,_⟩ := vertex_local_body i
  refine ⟨(fun v : RealPoint => realVertex i+v) ⁻¹' U,
    hU.preimage (continuous_const.add continuous_id), ?_, ?_⟩
  · simpa using hx
  · intro v hv
    exact (hbody _ hv).trans (cornerBodyCondition_add_vector i v)

theorem polygon_edge_local_cone (i : Fin 14) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    LocalConeGerm polygonBody (interpolate (realVertex i) (realVertex (next i)) t)
      (polygonBoundaryCone (.inr i)) := by
  let x := interpolate (realVertex i) (realVertex (next i)) t
  obtain ⟨U,hU,hx,hbody⟩ := outer_open_edge_local_halfplane i t ht ht'
  refine ⟨(fun v : RealPoint => x+v) ⁻¹' U,
    hU.preimage (continuous_const.add continuous_id), ?_, ?_⟩
  · simpa [x] using hx
  · intro v hv
    have hside : side (realVertex i) (realVertex (next i)) (x+v) =
        RealPoint.det (realEdge i) v := by
      rw [side_add_vector]
      have hz : side (realVertex i) (realVertex (next i)) x = 0 :=
        det_interpolate_self _ _ _
      rw [hz,zero_add]
      rfl
    simpa only [hside,polygonBoundaryCone,Set.mem_setOf_eq] using (hbody (x+v) hv).1

/-- Every native boundary slot has a whole-neighborhood cone formula, with no
placement, frame, tiling, or homochirality hypothesis. -/
theorem polygon_boundary_local_cone (b : BoundarySlot) (x : RealPoint)
    (hx : BoundarySlotAt b x) : LocalConeGerm polygonBody x (polygonBoundaryCone b) := by
  cases b with
  | inl i =>
      change x = realVertex i at hx
      subst x
      exact polygon_vertex_local_cone i
  | inr i =>
      obtain ⟨t,ht,ht',rfl⟩ := hx
      exact polygon_edge_local_cone i t ht ht'

theorem polygon_interior_local_cone (x : RealPoint) (hx : x ∈ interior polygonBody) :
    LocalConeGerm polygonBody x Set.univ := by
  refine ⟨(fun v : RealPoint => x+v) ⁻¹' interior polygonBody,
    isOpen_interior.preimage (continuous_const.add continuous_id), ?_, ?_⟩
  · simpa using hx
  · intro v hv
    exact iff_of_true (interior_subset hv) (Set.mem_univ v)

/-- All native points, including reflex corners and the retained straight
midpoint, are covered by these literal local cones. -/
theorem polygon_point_local_cone (x : RealPoint) (hx : x ∈ polygonBody) :
    ∃ C : Set RealPoint, LocalConeGerm polygonBody x C ∧
      (C = Set.univ ∨ ∃ b : BoundarySlot, BoundarySlotAt b x ∧ C = polygonBoundaryCone b) := by
  by_cases hi : x ∈ interior polygonBody
  · exact ⟨Set.univ,polygon_interior_local_cone x hi,Or.inl rfl⟩
  · have hf : x ∈ frontier polygonBody := ⟨subset_closure hx,hi⟩
    obtain ⟨b,hb⟩ := frontier_has_slot x hf
    exact ⟨polygonBoundaryCone b,polygon_boundary_local_cone b x hb,Or.inr ⟨b,hb,rfl⟩⟩

end
end SpectreGeometry
