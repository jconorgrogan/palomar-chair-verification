module

public import SpectreGeometry.PolygonProductKeyPairedMaterial

@[expose] public section


/-! Exact strict material and raw-carrier inequalities in the common signed
reference collar. These are statements about actual ambient interiors. -/
namespace SpectreGeometry
noncomputable section
open Set ProductKeyReference
open scoped InnerProductSpace

theorem product_key_signed_pose_image_collar_interior (s : ProductKeySite) :
    productKeySignedAffineIsometry s '' interior productKeyReferenceCollar =
      interior (productKeyCollar s) := by
  calc
    productKeySignedAffineIsometry s '' interior productKeyReferenceCollar =
        interior (productKeySignedAffineIsometry s '' productKeyReferenceCollar) :=
      (productKeySignedAffineIsometry s).toHomeomorph.image_interior _
    _ = interior (productKeyCollar s) := congrArg interior (product_key_signed_pose_image_collar s)

theorem product_key_signed_body_interior_iff (s : ProductKeySite) (w : EFour)
    (hw : w ∈ interior productKeyReferenceCollar) :
    productKeySignedAffineIsometry s w ∈ interior polygonProductKeyBody ↔
      productKeySign s * (w 3-referenceHeight s.1 * max 0 (coordinateEnvelope w)) < 0 := by
  have hc : productKeySignedAffineIsometry s w ∈ interior (productKeyCollar s) := by
    rw [← product_key_signed_pose_image_collar_interior]
    exact ⟨w,hw,rfl⟩
  rw [polygon_product_key_body_interior_local_iff s _ hc,
    product_key_signed_pose_outward_coordinate]
  have hh := signed_pose_tent_height s w
  cases hs : s.2.2 <;> simp [productKeySign,hs] at hh ⊢ <;>
    constructor <;> intro h <;> linarith

theorem product_key_signed_raw_interior_iff (s : ProductKeySite) (w : EFour)
    (hw : w ∈ interior productKeyReferenceCollar) :
    productKeySignedAffineIsometry s w ∈ interior polygonProductBody ↔ productKeySign s*w 3 < 0 := by
  have hc : productKeySignedAffineIsometry s w ∈ interior (productKeyCollar s) := by
    rw [← product_key_signed_pose_image_collar_interior]
    exact ⟨w,hw,rfl⟩
  rw [(product_key_collar_carrier_outward s _ (interior_subset hc)).2,
    product_key_signed_pose_outward_coordinate]

end
end SpectreGeometry
