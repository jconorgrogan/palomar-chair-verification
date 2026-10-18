module

public import LiteralPlanar.CurvedBodyTopology

@[expose] public section


/-! Exact frontier identification for the finite polynomial body. The fourteen
unit arcs retain all source endpoints, including the collinear midpoint. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry Forward

theorem tileMap_edgeCurve (e : Fin 14) (t : ℝ)
    (ht : -1/2 ≤ t) (ht' : t ≤ 1/2) :
    tileMap (euclideanCoordinates
      (interpolate (realVertex e) (realVertex (next e)) (t+1/2))) =
      euclideanCoordinates (Candidate.edgeCurve e t) := by
  rw [tileMap_on_edge e (t+1/2) (by linarith) (by linarith)]
  congr 1
  have he : t+1/2-1/2 = t := by ring
  simp only [deformedSegment,he,Candidate.edgeCurve,Candidate.leftNormal,quarterTurn]
  apply Prod.ext <;>
    simp only [interpolate,realEdge,RealPoint.sub,Prod.fst_add,Prod.snd_add,
      Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

theorem tileMap_image_edge (e : Fin 14) :
    tileMap '' euclideanEdge e =
      euclideanCoordinates '' (Candidate.edgeCurve e '' Set.Icc (-1/2 : ℝ) (1/2)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,⟨z,⟨t,ht,ht',rfl⟩,rfl⟩,rfl⟩
    refine ⟨Candidate.edgeCurve e (t-1/2),⟨t-1/2,⟨by linarith,by linarith⟩,rfl⟩,?_⟩
    have h := tileMap_edgeCurve e (t-1/2) (by linarith) (by linarith)
    rw [show t-1/2+1/2=t by ring] at h
    exact h.symm
  · rintro x ⟨y,⟨t,ht,rfl⟩,rfl⟩
    refine ⟨euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) (t+1/2)),
      ⟨_,⟨t+1/2,by linarith [ht.1],by linarith [ht.2],rfl⟩,rfl⟩,?_⟩
    exact tileMap_edgeCurve e t ht.1 ht.2

def curvedBoundary : Set EPlane := euclideanCoordinates '' Candidate.candidateBoundary

end
end LiteralPlanar.FanBounds

namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry FanBounds
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p)

theorem tileHomeomorph_image_edge (i : I) (e : Fin 14) :
    tileHomeomorph p T i '' euclideanEdge e =
      euclideanCoordinates '' (Candidate.edgeCurve e '' Set.Icc (-1/2 : ℝ) (1/2)) := by
  rw [←tileMap_image_edge]
  apply Set.image_congr
  intro x hx
  apply tileHomeomorph_on_body p T i x
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨y,Set.mem_iUnion.mpr ⟨e,polygonEdge_mem_triangleBody e hy⟩,rfl⟩

include p T in
theorem curvedBody_frontier (i : I) : frontier curvedBody = curvedBoundary := by
  rw [←tileHomeomorph_image_body p T i,←(tileHomeomorph p T i).image_frontier,
    euclideanBody_frontier_eq_edges,Set.image_iUnion]
  simp only [tileHomeomorph_image_edge,curvedBoundary,Candidate.candidateBoundary,Set.image_iUnion]

end
end LiteralPlanar.Forward
