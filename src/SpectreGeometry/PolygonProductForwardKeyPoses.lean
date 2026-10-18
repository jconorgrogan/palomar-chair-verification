module

public import SpectreGeometry.PolygonProductIsometries
public import SpectreGeometry.PolygonProductPoseFromCoordinates
public import SpectreGeometry.DirectEdgeFrameTransport

@[expose] public section


namespace SpectreGeometry
noncomputable section

/-- Reversed proper edge endpoints transport the whole normal edge chart. -/
theorem proper_reversed_edge_frame (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (i j : Fin 14)
    (ha : f (euclideanVertex i) = g (euclideanVertex (next j)))
    (hb : f (euclideanVertex (next i)) = g (euclideanVertex j)) (r h : ℝ) :
    f (euclideanCoordinates (productEdgeFramePoint i r h)) =
      g (euclideanCoordinates (productEdgeFramePoint j (1-r) (-h))) := by
  have he := direct_edge_frame_transport f g hf hg
    (realVertex i) (realVertex (next i)) (realVertex (next j)) (realVertex j) ha hb r (-h)
  have hl : realVertex i+r • (realVertex (next i)-realVertex i)+
      (-h) • quarterTurn (realVertex (next i)-realVertex i) = productEdgeFramePoint i r h := by
    apply Prod.ext <;> simp [productEdgeFramePoint,realEdge,RealPoint.sub,quarterTurn] <;> ring
  have hr : realVertex (next j)+r • (realVertex j-realVertex (next j))+
      (-h) • quarterTurn (realVertex j-realVertex (next j)) =
      productEdgeFramePoint j (1-r) (-h) := by
    apply Prod.ext <;> simp [productEdgeFramePoint,realEdge,RealPoint.sub,quarterTurn] <;> ring
  simpa only [hl,hr] using he

/-- A reversed active left edge and unchanged passive placement align each
literal quarter-edge key with its opposite-polarity mate. -/
theorem product_left_key_pose (f g q : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (i j : Fin 14) (e : Bool)
    (ha : f (euclideanVertex i) = g (euclideanVertex (next j)))
    (hb : f (euclideanVertex (next i)) = g (euclideanVertex j)) :
    (productKeySignedAffineIsometry (0,i,e)).toIsometryEquiv.trans (productPlacement f q) =
      (productKeySignedAffineIsometry (0,j,!e)).toIsometryEquiv.trans (productPlacement g q) := by
  apply product_key_pose_of_full_coordinates
  · cases e <;> norm_num [productKeySign]
  · intro r h p
    change productPlacement f q (euclideanProductCoordinates
      (euclideanCoordinates (productEdgeFramePoint i r h),euclideanCoordinates p)) =
      productPlacement g q (euclideanProductCoordinates
      (euclideanCoordinates (productEdgeFramePoint j (1-r) (-h)),euclideanCoordinates p))
    rw [productPlacement_apply,productPlacement_apply,proper_reversed_edge_frame f g hf hg i j ha hb]

/-- The corresponding right-factor key pairing. -/
theorem product_right_key_pose (f g q : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (i j : Fin 14) (e : Bool)
    (ha : f (euclideanVertex i) = g (euclideanVertex (next j)))
    (hb : f (euclideanVertex (next i)) = g (euclideanVertex j)) :
    (productKeySignedAffineIsometry (1,i,e)).toIsometryEquiv.trans (productPlacement q f) =
      (productKeySignedAffineIsometry (1,j,!e)).toIsometryEquiv.trans (productPlacement q g) := by
  apply product_key_pose_of_full_coordinates
  · cases e <;> norm_num [productKeySign]
  · intro r h p
    change productPlacement q f (euclideanProductCoordinates
      (euclideanCoordinates p,euclideanCoordinates (productEdgeFramePoint i r h))) =
      productPlacement q g (euclideanProductCoordinates
      (euclideanCoordinates p,euclideanCoordinates (productEdgeFramePoint j (1-r) (-h))))
    rw [productPlacement_apply,productPlacement_apply,proper_reversed_edge_frame f g hf hg i j ha hb]

end
end SpectreGeometry
