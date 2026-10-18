module

public import LiteralPlanar.CurvedArcMates

@[expose] public section


/-! A strict point on each literal polynomial arc has an actual open body
frontier neighborhood containing no other arc. The proof uses the exhibited
ambient fan homeomorphism and the checked source-edge fan separation. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem strict_curve_point_not_other_arc (e j : Fin 14) (hej : e ≠ j)
    (t : ℝ) (ht : -1/2 < t) (ht' : t < 1/2) :
    euclideanCoordinates (edgeCurve e t) ∉ euclideanArc j := by
  have hs : interpolate (realVertex e) (realVertex (next e)) (t+1/2) ∈ polygonEdge e :=
    ⟨t+1/2,by linarith,by linarith,rfl⟩
  have hb : euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) (t+1/2)) ∈
      euclideanBody := ⟨_,mem_iUnion.mpr ⟨e,polygonEdge_mem_triangleBody e hs⟩,rfl⟩
  have hpoint : tileHomeomorph p T root
      (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) (t+1/2))) =
      euclideanCoordinates (edgeCurve e t) := by
    rw [tileHomeomorph_on_body p T root _ hb,tileMap_edgeCurve e t ht.le ht'.le]
  intro hx
  have himage : tileHomeomorph p T root '' euclideanEdge j = euclideanArc j :=
    tileHomeomorph_image_edge p T root j
  rw [←himage] at hx
  obtain ⟨y,hy,he⟩ := hx
  have heq := (tileHomeomorph p T root).injective (he.trans hpoint.symm)
  rw [heq] at hy
  obtain ⟨z,hz,hez⟩ := hy
  have hzz := euclideanCoordinates.injective hez
  rw [hzz] at hz
  exact outer_open_edge_not_other_triangle e j hej (t+1/2) (by linarith) (by linarith)
    (polygonEdge_mem_triangleBody j hz)

theorem strict_curve_local_frontier (e : Fin 14) (t : ℝ)
    (ht : -1/2 < t) (ht' : t < 1/2) :
    ∃ U : Set EPlane, IsOpen U ∧ euclideanCoordinates (edgeCurve e t) ∈ U ∧
      frontier curvedBody ∩ U = euclideanArc e ∩ U := by
  classical
  let O : Set EPlane := ⋃ j : {j : Fin 14 // j ≠ e}, euclideanArc j
  have hO : IsClosed O := isClosed_iUnion_of_finite
    (fun j => (euclideanArc_compact j).isClosed)
  have hx : euclideanCoordinates (edgeCurve e t) ∉ O := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    exact strict_curve_point_not_other_arc p T root e j j.property.symm t ht ht' hj
  refine ⟨Oᶜ,hO.isOpen_compl,hx,?_⟩
  have hf : frontier curvedBody = ⋃ j : Fin 14, euclideanArc j := by
    rw [curvedBody_frontier p T root]
    simp only [curvedBoundary,candidateBoundary,Set.image_iUnion,euclideanArc]
  rw [hf]
  apply Set.Subset.antisymm
  · rintro x ⟨hj,hx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hj
    by_cases he : j=e
    · exact ⟨he ▸ hj,hx⟩
    · exact (hx (mem_iUnion.mpr ⟨⟨j,he⟩,hj⟩)).elim
  · rintro x ⟨he,hx⟩
    exact ⟨mem_iUnion.mpr ⟨e,he⟩,hx⟩

end
end LiteralPlanar.Forward
