module

public import LiteralPlanar.LiteralCandidate
public import LiteralPlanar.EuclideanArcRigidity

@[expose] public section


/-! Each literal boundary arc is exactly an isometric image of the canonical
quintic arc. This is independent of any body-frontier or tiling assertion. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

def edgeMidpoint (e : Fin 14) : RealPoint :=
  realVertex e + (1/2 : ℝ) • realEdge e

def edgeChart (e : Fin 14) : EPlane ≃ᵢ EPlane :=
  (euclideanRotation (edgeTurn e)).trans
    (IsometryEquiv.addRight (euclideanCoordinates (edgeMidpoint e)))

theorem edgeChart_apply (e : Fin 14) (p : RealPoint) :
    edgeChart e (euclideanCoordinates p) = euclideanCoordinates
      (edgeMidpoint e + p.1 • realEdge e + p.2 • quarterTurn (realEdge e)) := by
  change coordinateLinearEquiv (rotate (edgeTurn e)
      (coordinateLinearEquiv.symm (coordinateLinearEquiv p))) +
      coordinateLinearEquiv (edgeMidpoint e) = coordinateLinearEquiv _
  rw [coordinateLinearEquiv.symm_apply_apply,←map_add]
  congr 1
  rw [rotate,←real_edge_direction]
  apply Prod.ext <;>
    simp only [complexMulReal,quarterTurn,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

theorem edgeChart_graph (e : Fin 14) (t : ℝ) :
    edgeChart e (euclideanCoordinates (t,Quintic.height Quintic.amplitude t)) =
      euclideanCoordinates (edgeCurve e t) := by
  rw [edgeChart_apply]
  congr 1
  apply Prod.ext <;>
    simp only [edgeMidpoint,edgeCurve,leftNormal,quarterTurn,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

def euclideanArc (e : Fin 14) : Set EPlane :=
  euclideanCoordinates '' (edgeCurve e '' Set.Icc (-1/2 : ℝ) (1/2))

theorem euclideanArc_eq_chart_image (e : Fin 14) :
    euclideanArc e = edgeChart e '' Quintic.standardArc Quintic.amplitude := by
  simp only [euclideanArc,Quintic.standardArc,Set.image_image]
  apply Set.image_congr
  intro t ht
  exact (edgeChart_graph e t).symm

end
end LiteralPlanar.Candidate
