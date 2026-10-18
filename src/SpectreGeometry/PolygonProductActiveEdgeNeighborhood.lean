module

public import SpectreGeometry.PolygonProductKeyFactorTransition

@[expose] public section


/-! Whole reversed unit-edge registration supplies a genuine two-tile open
neighborhood at every strict edge point. No local covering or halfspace
certificate is an input; the literal polygon edge neighborhoods supply it. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem product_edge_frame_side (i : Fin 14) (r h : ℝ) :
    side (realVertex i) (realVertex (next i)) (productEdgeFramePoint i r h) = -h := by
  have hu := real_edges_unit_squared i
  have hh := congrArg (fun t : ℝ => t*h) hu
  change RealPoint.det (realEdge i) (productEdgeFramePoint i r h-realVertex i) = -h
  simp only [productEdgeFramePoint,RealPoint.det,RealPoint.dot,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at *
  nlinarith

theorem product_active_edge_transition_side (i j : Fin 14) (a : RealPoint) :
    side (realVertex j) (realVertex (next j))
      (euclideanCoordinates.symm (productActiveEdgeTransition i j (euclideanCoordinates a))) =
      -side (realVertex i) (realVertex (next i)) a := by
  obtain ⟨r,h,rfl⟩ := product_edge_frame_surjective i a
  rw [product_active_edge_transition_frame,Homeomorph.symm_apply_apply,
    product_edge_frame_side,product_edge_frame_side]

theorem product_edge_frame_zero_interpolate (i : Fin 14) (r : ℝ) :
    productEdgeFramePoint i r 0 = interpolate (realVertex i) (realVertex (next i)) r := by
  apply Prod.ext <;> simp [productEdgeFramePoint,interpolate,realEdge,RealPoint.sub] <;> ring

theorem product_active_edge_transition_interpolate (i j : Fin 14) (r : ℝ) :
    productActiveEdgeTransition i j (euclideanCoordinates
      (interpolate (realVertex i) (realVertex (next i)) r)) =
      euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) (1-r)) := by
  rw [← product_edge_frame_zero_interpolate,product_active_edge_transition_frame]
  simpa only [neg_zero] using congrArg euclideanCoordinates (product_edge_frame_zero_interpolate j (1-r))

private theorem placed_open_edge_local_body (A : EPlane ≃ᵢ EPlane) (i : Fin 14)
    (r : ℝ) (hr : 0 < r) (hr' : r < 1) :
    ∃ U : Set EPlane, IsOpen U ∧
      A (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) r)) ∈ U ∧
      ∀ y ∈ U, (y ∈ A '' euclideanBody ↔ 0 ≤ placedSide A i y) := by
  obtain ⟨U,hU,hx,hl⟩ := outer_open_edge_local_halfplane i r hr hr'
  let H : RealPoint ≃ₜ EPlane := euclideanCoordinates.trans A.toHomeomorph
  refine ⟨H '' U,H.isOpenMap _ hU,⟨_,hx,rfl⟩,?_⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := hy
  have hid : A '' euclideanBody = H '' polygonBody := by
    rw [euclideanBody,Set.image_image]
    rfl
  rw [hid,H.injective.mem_set_image]
  have hs : placedSide A i (H z) = side (realVertex i) (realVertex (next i)) z := by
    unfold placedSide H
    simp only [Homeomorph.trans_apply,IsometryEquiv.coe_toHomeomorph,
      A.symm_apply_apply,euclideanCoordinates.symm_apply_apply]
  rw [hs]
  exact (hl z hz).1

theorem registered_active_placed_sides_opposite (A B : EPlane ≃ᵢ EPlane) (i j : Fin 14)
    (hab : ∀ a : RealPoint, A (euclideanCoordinates a) =
      B (productActiveEdgeTransition i j (euclideanCoordinates a))) (y : EPlane) :
    placedSide B j y = -placedSide A i y := by
  obtain ⟨z,rfl⟩ := A.surjective y
  obtain ⟨a,rfl⟩ := euclideanCoordinates.surjective z
  have he := hab a
  change side (realVertex j) (realVertex (next j)) (euclideanCoordinates.symm
      (B.symm (A (euclideanCoordinates a)))) =
    -side (realVertex i) (realVertex (next i)) (euclideanCoordinates.symm
      (A.symm (A (euclideanCoordinates a))))
  rw [A.symm_apply_apply,Homeomorph.symm_apply_apply,he,B.symm_apply_apply]
  exact product_active_edge_transition_side i j a

theorem registered_active_edge_mem_interior_union (A B : EPlane ≃ᵢ EPlane) (i j : Fin 14)
    (hab : ∀ a : RealPoint, A (euclideanCoordinates a) =
      B (productActiveEdgeTransition i j (euclideanCoordinates a)))
    (r : ℝ) (hr : 0 < r) (hr' : r < 1) :
    A (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) r)) ∈
      interior ((A '' euclideanBody) ∪ (B '' euclideanBody)) := by
  obtain ⟨U,hU,hxU,hA⟩ := placed_open_edge_local_body A i r hr hr'
  obtain ⟨V,hV,hxV,hB⟩ := placed_open_edge_local_body B j (1-r) (by linarith) (by linarith)
  have he := hab (interpolate (realVertex i) (realVertex (next i)) r)
  rw [product_active_edge_transition_interpolate] at he
  have hsub : U ∩ V ⊆ (A '' euclideanBody) ∪ (B '' euclideanBody) := by
    intro y hy
    by_cases hs : 0 ≤ placedSide A i y
    · exact Or.inl ((hA y hy.1).mpr hs)
    · apply Or.inr
      apply (hB y hy.2).mpr
      rw [registered_active_placed_sides_opposite A B i j hab]
      linarith
  exact interior_maximal hsub (hU.inter hV) ⟨hxU,he.symm ▸ hxV⟩

end
end SpectreGeometry
