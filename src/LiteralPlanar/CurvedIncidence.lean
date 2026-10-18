module

public import LiteralPlanar.CurvedArcIsolation

@[expose] public section


/-! Actual curved boundary incidence, retaining every original vertex,
including the collinear midpoint. No edge-to-edge tiling assumption is made. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem edgeCurve_left (e : Fin 14) : edgeCurve e (-1/2) = realVertex e := by
  simp only [edgeCurve,Quintic.height_left,show (-1/2 : ℝ)+1/2=0 by norm_num,zero_smul,add_zero]

theorem edgeCurve_right (e : Fin 14) : edgeCurve e (1/2) = realVertex (next e) := by
  simp only [edgeCurve,Quintic.height_right,show (1/2 : ℝ)+1/2=1 by norm_num,
    one_smul,zero_smul,add_zero]
  change realVertex e+(realVertex (next e)-realVertex e)=realVertex (next e)
  abel

theorem euclideanCurve_injective (e : Fin 14) :
    Function.Injective (fun t : ℝ => euclideanCoordinates (edgeCurve e t)) := by
  intro s t h
  change euclideanCoordinates (edgeCurve e s) = euclideanCoordinates (edgeCurve e t) at h
  rw [←edgeChart_graph,←edgeChart_graph] at h
  exact (Quintic.standardArc_parameter_injective Quintic.amplitude)
    ((edgeChart e).injective h)

theorem curved_vertex_mem_arc (e : Fin 14) : euclideanVertex e ∈ euclideanArc e := by
  exact ⟨realVertex e,⟨-1/2,⟨le_rfl,by norm_num⟩,edgeCurve_left e⟩,rfl⟩

end
end LiteralPlanar.Candidate

namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem tileHomeomorph_at_vertex (e : Fin 14) :
    tileHomeomorph p T root (euclideanVertex e) = euclideanVertex e := by
  change tileHomeomorph p T root (euclideanCoordinates (realVertex e)) =
    euclideanCoordinates (realVertex e)
  rw [tileHomeomorph_on_body p T root _
    ⟨realVertex e,mem_iUnion.mpr ⟨e,polygonEdge_mem_triangleBody e (vertex_mem_polygonEdge e)⟩,rfl⟩]
  change euclideanVertex e + tileResidual (euclideanVertex e) = euclideanVertex e
  rw [tileResidual_at_vertex,add_zero]

theorem strict_curve_point_not_vertex (e v : Fin 14) (t : ℝ)
    (ht : -1/2 < t) (ht' : t < 1/2) :
    euclideanCoordinates (edgeCurve e t) ≠ euclideanVertex v := by
  intro he
  by_cases hv : v=e
  · rw [hv] at he
    have hh : euclideanCoordinates (edgeCurve e t) = euclideanCoordinates (edgeCurve e (-1/2)) := by
      simpa only [edgeCurve_left,euclideanVertex] using he
    have ht0 := euclideanCurve_injective e hh
    linarith
  · exact strict_curve_point_not_other_arc p T root e v (Ne.symm hv) t ht ht'
      (he.symm ▸ curved_vertex_mem_arc v)

theorem curved_nonvertex_frontier_arc (f : EPlane ≃ᵢ EPlane) (x : EPlane)
    (hx : x ∈ frontier (f '' curvedBody))
    (hvertex : ∀ e : Fin 14, x ≠ f (euclideanVertex e)) :
    ∃ e : Fin 14, ∃ t : ℝ, -1/2 < t ∧ t < 1/2 ∧
      x = f (euclideanCoordinates (edgeCurve e t)) := by
  have hf : frontier (f '' curvedBody) = ⋃ e : Fin 14, f '' euclideanArc e := by
    simp only [←IsometryEquiv.coe_toHomeomorph f]
    rw [←f.toHomeomorph.image_frontier,curvedBody_frontier p T root]
    simp only [curvedBoundary,candidateBoundary,Set.image_iUnion,euclideanArc,Set.image_image]
  rw [hf] at hx
  obtain ⟨e,hx⟩ := mem_iUnion.mp hx
  obtain ⟨y,⟨z,⟨t,ht,rfl⟩,rfl⟩,rfl⟩ := hx
  have hleft : t ≠ -1/2 := by
    intro he
    exact hvertex e (by simp only [he,edgeCurve_left,euclideanVertex])
  have hright : t ≠ 1/2 := by
    intro he
    exact hvertex (next e) (by simp only [he,edgeCurve_right,euclideanVertex])
  exact ⟨e,t,lt_of_le_of_ne ht.1 (Ne.symm hleft),lt_of_le_of_ne ht.2 hright,rfl⟩

end
end LiteralPlanar.Forward
