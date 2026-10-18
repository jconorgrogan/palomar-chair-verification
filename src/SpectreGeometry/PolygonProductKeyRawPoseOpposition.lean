module

public import SpectreGeometry.PolygonProductKeyPairedMaterialInterior

@[expose] public section


/-! The retained inward point also lies inside the original raw carrier.
Raw packing therefore forces opposite signed poses. Conversely, a registered
opposite-sign equal-label pair has disjoint actual material interiors inside
its common collar, supplying the local reverse-surgery implication. -/
namespace SpectreGeometry
noncomputable section
open Set ProductKeyReference
open scoped InnerProductSpace

private theorem raw_castSucc_ne_three (j : Fin 3) : j.castSucc ≠ (3 : Fin 4) := by
  intro h
  have he := congrArg Fin.val h
  have hj := j.isLt
  change j.val = 3 at he
  omega

theorem product_key_inward_reference_mem_raw_interior (s : ProductKeySite) :
    productKeySignedAffineIsometry s (productKeyInwardReferencePoint s) ∈
      interior polygonProductBody := by
  let x := productKeySignedAffineIsometry s (productKeyInwardReferencePoint s)
  have ht (j : Fin 3) : inner ℝ (productKeyTangent s j) (x-productKeyCenter s) = 0 := by
    rw [product_key_signed_pose_tangent_coordinate]
    simp [productKeyInwardReferencePoint,raw_castSucc_ne_three j]
  have hn : inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) = -productKeyRho/2 := by
    rw [product_key_signed_pose_outward_coordinate]
    cases hs : s.2.2 <;> simp [productKeyInwardReferencePoint,productKeySign,hs] <;> ring
  have hc : x ∈ interior (productKeyCollar s) := by
    apply product_key_strict_collar_subset_interior s
    constructor
    · intro j; rw [ht]; norm_num [productKeyEta]
    · rw [hn]; norm_num [productKeyRho]
  apply (product_key_collar_carrier_outward s x (interior_subset hc)).2.mpr
  rw [hn]
  norm_num [productKeyRho]

/-- Exact full signed-pose coincidence in a packing forces opposite recipe
polarities. Neither absolute-label equality nor contact recognition is an input. -/
theorem coincident_signed_poses_raw_opposite_signs (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour)
    (hd : Disjoint (interior (f '' polygonProductBody)) (interior (g '' polygonProductBody)))
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g) :
    productKeySign t = -productKeySign s := by
  have hne : productKeySign s ≠ productKeySign t := by
    intro he
    have hw : productKeyInwardReferencePoint s = productKeyInwardReferencePoint t := by
      simp only [productKeyInwardReferencePoint,he]
    have hpoint := congrArg (fun h : EFour ≃ᵢ EFour => h (productKeyInwardReferencePoint s)) hp
    change f (productKeySignedAffineIsometry s (productKeyInwardReferencePoint s)) =
      g (productKeySignedAffineIsometry t (productKeyInwardReferencePoint s)) at hpoint
    rw [hw] at hpoint
    have hi := f.toHomeomorph.isOpenMap.image_interior_subset polygonProductBody
      ⟨_,product_key_inward_reference_mem_raw_interior s,rfl⟩
    have hj := g.toHomeomorph.isOpenMap.image_interior_subset polygonProductBody
      ⟨_,product_key_inward_reference_mem_raw_interior t,rfl⟩
    rw [← hw] at hpoint
    have hpoint' : f (productKeySignedAffineIsometry s (productKeyInwardReferencePoint s)) =
        g (productKeySignedAffineIsometry t (productKeyInwardReferencePoint t)) := by
      simpa only [hw] using hpoint
    exact Set.disjoint_left.mp hd hi (hpoint'.symm ▸ hj)
  cases hs : s.2.2 <;> cases ht : t.2.2 <;> simp_all [productKeySign]

private theorem raw_isometry_mem_interior_image (f : EFour ≃ᵢ EFour) (S : Set EFour) (z : EFour) :
    f z ∈ interior (f '' S) ↔ z ∈ interior S := by
  have he : f '' interior S = interior (f '' S) := f.toHomeomorph.image_interior S
  rw [← he]
  constructor
  · rintro ⟨y,hy,he⟩
    exact (f.injective he) ▸ hy
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem paired_actual_interiors_disjoint_on_collar (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour) (hlabel : s.1 = t.1)
    (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g)
    (x : EFour) (hx : x ∈ interior (f '' productKeyCollar s)) :
    ¬ (x ∈ interior (f '' polygonProductKeyBody) ∧ x ∈ interior (g '' polygonProductKeyBody)) := by
  have hi : f '' interior (productKeyCollar s) = interior (f '' productKeyCollar s) :=
    f.toHomeomorph.image_interior (productKeyCollar s)
  rw [← hi,← product_key_signed_pose_image_collar_interior s,Set.image_image] at hx
  obtain ⟨w,hw,rfl⟩ := hx
  rintro ⟨hi,hj⟩
  have he := congrArg (fun h : EFour ≃ᵢ EFour => h w) hp
  change f (productKeySignedAffineIsometry s w) = g (productKeySignedAffineIsometry t w) at he
  have hi' := (raw_isometry_mem_interior_image f polygonProductKeyBody _).mp hi
  change f (productKeySignedAffineIsometry s w) ∈ interior (g '' polygonProductKeyBody) at hj
  rw [he] at hj
  have hj' := (raw_isometry_mem_interior_image g polygonProductKeyBody _).mp hj
  have hs := (product_key_signed_body_interior_iff s w hw).mp hi'
  have ht := (product_key_signed_body_interior_iff t w hw).mp hj'
  rw [← hlabel,hsign,neg_mul] at ht
  linarith

end
end SpectreGeometry
