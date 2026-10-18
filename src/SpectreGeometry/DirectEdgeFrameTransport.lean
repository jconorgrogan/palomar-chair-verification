module

public import SpectreGeometry.DirectIsometryFrames

@[expose] public section


namespace SpectreGeometry
noncomputable section

/-- Proper planar isometries commute with the fixed positive quarter-turn
on displacement vectors. -/
theorem direct_coordinateAction_quarterTurn (f : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (x : RealPoint) :
    coordinateAction f (quarterTurn x) = quarterTurn (coordinateAction f x) := by
  rw [direct_coordinateAction f hf,direct_coordinateAction f hf]
  apply Prod.ext <;> simp [complexMulReal,quarterTurn] <;> ring

/-- Endpoint agreement determines the complete oriented affine edge frame,
including normal displacements. No discrete rotation assumption is used. -/
theorem direct_edge_frame_transport (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g)
    (a b c d : RealPoint)
    (ha : f (euclideanCoordinates a) = g (euclideanCoordinates c))
    (hb : f (euclideanCoordinates b) = g (euclideanCoordinates d))
    (r h : ℝ) :
    f (euclideanCoordinates (a + r • (b-a) + h • quarterTurn (b-a))) =
      g (euclideanCoordinates (c + r • (d-c) + h • quarterTurn (d-c))) := by
  apply euclideanCoordinates.symm.injective
  have he : coordinateAction f (b-a) = coordinateAction g (d-c) := by
    rw [coordinateAction_sub,coordinateAction_sub,ha,hb]
  have hn : coordinateAction f (quarterTurn (b-a)) =
      coordinateAction g (quarterTurn (d-c)) := by
    rw [direct_coordinateAction_quarterTurn f hf,
      direct_coordinateAction_quarterTurn g hg,he]
  have hs := coordinateAction_sub f a (a+r • (b-a)+h • quarterTurn (b-a))
  have ht := coordinateAction_sub g c (c+r • (d-c)+h • quarterTurn (d-c))
  have hfsub : a+r • (b-a)+h • quarterTurn (b-a)-a =
      r • (b-a)+h • quarterTurn (b-a) := by abel
  have hgsub : c+r • (d-c)+h • quarterTurn (d-c)-c =
      r • (d-c)+h • quarterTurn (d-c) := by abel
  rw [hfsub,map_add,map_smul,map_smul,he,hn] at hs
  rw [hgsub,map_add,map_smul,map_smul] at ht
  rw [ha] at hs
  exact sub_left_injective (hs.symm.trans ht)

end
end SpectreGeometry
