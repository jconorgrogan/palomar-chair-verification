module

public import SpectreGeometry.PolygonProductKeyPoseOpposition
public import SpectreGeometry.PolygonProductWholeKeyBinding
public import SpectreGeometry.PolygonProductKeyCollarBoundary

@[expose] public section


/-! Exact local material and raw-carrier partitions in a genuinely paired
world collar. The actual signed max-min height is used on the whole closed
collar, including its boundary and the zero-extended footprint. -/
namespace SpectreGeometry
noncomputable section
open Set ProductKeyReference
open scoped InnerProductSpace

theorem product_key_signed_body_iff (s : ProductKeySite) (w : EFour)
    (hw : w ∈ productKeyReferenceCollar) :
    productKeySignedAffineIsometry s w ∈ polygonProductKeyBody ↔
      productKeySign s * (w 3-referenceHeight s.1 * max 0 (coordinateEnvelope w)) ≤ 0 := by
  have hc : productKeySignedAffineIsometry s w ∈ productKeyCollar s := by
    rw [← product_key_signed_pose_image_collar]
    exact ⟨w,hw,rfl⟩
  rw [polygon_product_key_body_collar_iff s _ hc]
  change inner ℝ (productKeyOutwardNormal s) (productKeySignedAffineIsometry s w-productKeyCenter s) ≤
    productKeyHeight s (productKeySignedAffineIsometry s w-productKeyCenter s) ↔ _
  rw [product_key_signed_pose_outward_coordinate]
  have hh := signed_pose_tent_height s w
  cases hs : s.2.2 <;> simp [productKeySign,hs] at hh ⊢ <;>
    constructor <;> intro h <;> linarith

theorem product_key_signed_raw_iff (s : ProductKeySite) (w : EFour)
    (hw : w ∈ productKeyReferenceCollar) :
    productKeySignedAffineIsometry s w ∈ polygonProductBody ↔ productKeySign s*w 3 ≤ 0 := by
  have hc : productKeySignedAffineIsometry s w ∈ productKeyCollar s := by
    rw [← product_key_signed_pose_image_collar]
    exact ⟨w,hw,rfl⟩
  rw [(product_key_collar_carrier_outward s _ hc).1,product_key_signed_pose_outward_coordinate]

/-- The actual bodies of the matched pair fill their entire common collar. -/
theorem paired_actual_bodies_cover_collar (s t : ProductKeySite) (f g : EFour ≃ᵢ EFour)
    (hlabel : s.1 = t.1) (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g) :
    f '' productKeyCollar s ⊆ (f '' polygonProductKeyBody) ∪ (g '' polygonProductKeyBody) := by
  intro x hx
  rw [← product_key_signed_pose_image_collar s,Set.image_image] at hx
  obtain ⟨w,hw,rfl⟩ := hx
  have he := congrArg (fun h : EFour ≃ᵢ EFour => h w) hp
  change f (productKeySignedAffineIsometry s w) = g (productKeySignedAffineIsometry t w) at he
  have hcases : productKeySignedAffineIsometry s w ∈ polygonProductKeyBody ∨
      productKeySignedAffineIsometry t w ∈ polygonProductKeyBody := by
    rw [product_key_signed_body_iff s w hw,product_key_signed_body_iff t w hw,← hlabel,hsign]
    simpa only [neg_mul,neg_nonpos] using
      le_total (productKeySign s*(w 3-referenceHeight s.1*max 0 (coordinateEnvelope w))) 0
  rcases hcases with hs | ht
  · exact Or.inl ⟨_,hs,rfl⟩
  · exact Or.inr ⟨_,ht,he.symm⟩

/-- The corresponding original product carriers fill that same collar. -/
theorem paired_raw_bodies_cover_collar (s t : ProductKeySite) (f g : EFour ≃ᵢ EFour)
    (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g) :
    f '' productKeyCollar s ⊆ (f '' polygonProductBody) ∪ (g '' polygonProductBody) := by
  intro x hx
  rw [← product_key_signed_pose_image_collar s,Set.image_image] at hx
  obtain ⟨w,hw,rfl⟩ := hx
  have he := congrArg (fun h : EFour ≃ᵢ EFour => h w) hp
  change f (productKeySignedAffineIsometry s w) = g (productKeySignedAffineIsometry t w) at he
  have hcases : productKeySignedAffineIsometry s w ∈ polygonProductBody ∨
      productKeySignedAffineIsometry t w ∈ polygonProductBody := by
    rw [product_key_signed_raw_iff s w hw,product_key_signed_raw_iff t w hw,hsign]
    simpa only [neg_mul,neg_nonpos] using le_total (productKeySign s*w 3) 0
  rcases hcases with hs | ht
  · exact Or.inl ⟨_,hs,rfl⟩
  · exact Or.inr ⟨_,ht,he.symm⟩

end
end SpectreGeometry
