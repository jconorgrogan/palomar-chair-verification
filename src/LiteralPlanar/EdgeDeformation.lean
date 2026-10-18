module

public import LiteralPlanar.FanTileMapImage
public import SpectreGeometry.DirectEdgeFrameTransport

@[expose] public section


/-! Exact compatibility of the literal quintic edge deformation under proper
isometries with reversed endpoint matches. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry

def deformedSegment (a b : RealPoint) (t : ℝ) : RealPoint :=
  interpolate a b t + Quintic.height Quintic.amplitude (t - 1/2) • quarterTurn (b-a)

theorem deformedSegment_reverse (a b : RealPoint) (t : ℝ) :
    deformedSegment b a (1-t) = deformedSegment a b t := by
  have ht : 1-t-1/2 = -(t-1/2) := by ring
  simp only [deformedSegment, ht, Quintic.height_neg]
  apply Prod.ext <;>
    simp only [interpolate, quarterTurn, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem tileMap_on_edge (e : Fin 14) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    tileMap (euclideanCoordinates
      (interpolate (realVertex e) (realVertex (next e)) t)) =
      euclideanCoordinates (deformedSegment (realVertex e) (realVertex (next e)) t) := by
  rw [tileMap, tileResidual_on_edge e t ht ht']
  change coordinateLinearEquiv _ + _ • coordinateLinearEquiv _ = coordinateLinearEquiv _
  rw [←map_smul, ←map_add]
  rfl

theorem proper_deformed_edges_reversed (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (e j : Fin 14)
    (ha : f (euclideanVertex e) = g (euclideanVertex (next j)))
    (hb : f (euclideanVertex (next e)) = g (euclideanVertex j)) (t : ℝ) :
    f (euclideanCoordinates (deformedSegment (realVertex e) (realVertex (next e)) t)) =
      g (euclideanCoordinates (deformedSegment (realVertex j) (realVertex (next j)) (1-t))) := by
  rw [deformedSegment_reverse]
  have h := direct_edge_frame_transport f g hf hg
    (realVertex e) (realVertex (next e)) (realVertex (next j)) (realVertex j)
    ha hb t (Quintic.height Quintic.amplitude (t-1/2))
  have he (a b : RealPoint) : interpolate a b t = a + t • (b-a) := by
    apply Prod.ext <;> simp [interpolate] <;> ring
  simpa only [deformedSegment, he] using h

/-- The full deformed image agrees at every point of a registered shared edge,
including its two endpoints. -/
theorem placed_tileMap_on_reversed_edge (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (e j : Fin 14)
    (ha : f (euclideanVertex e) = g (euclideanVertex (next j)))
    (hb : f (euclideanVertex (next e)) = g (euclideanVertex j))
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    f (tileMap (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) =
      g (tileMap (euclideanCoordinates
        (interpolate (realVertex j) (realVertex (next j)) (1-t)))) := by
  rw [tileMap_on_edge e t ht ht', tileMap_on_edge j (1-t) (by linarith) (by linarith)]
  exact proper_deformed_edges_reversed f g hf hg e j ha hb t

end
end LiteralPlanar.FanBounds
