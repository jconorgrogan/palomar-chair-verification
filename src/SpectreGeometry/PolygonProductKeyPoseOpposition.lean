module

public import SpectreGeometry.PolygonProductKeySignedPoses
public import SpectreGeometry.PolygonProductKeyFrontier

@[expose] public section


/-! Literal material-side information from coincident signed reference poses.
A fixed point strictly inward from each actual collar rules out equal recipe
polarity in two interior-disjoint copies. Full collar coincidence follows
from the signed frame and the actual symmetric reference box. -/
namespace SpectreGeometry
noncomputable section
open Set
open scoped InnerProductSpace

def productKeyInwardReferencePoint (s : ProductKeySite) : EFour :=
  WithLp.toLp 2 (fun j : Fin 4 => if j = 3 then -productKeySign s*(productKeyRho/2) else 0)

private theorem castSucc_ne_three (j : Fin 3) : j.castSucc ≠ (3 : Fin 4) := by
  intro h
  have he := congrArg Fin.val h
  have hj := j.isLt
  change j.val = 3 at he
  omega

/-- One exact reference-coordinate point is strictly inside the actual body. -/
theorem product_key_inward_reference_mem_interior (s : ProductKeySite) :
    productKeySignedAffineIsometry s (productKeyInwardReferencePoint s) ∈
      interior polygonProductKeyBody := by
  let x := productKeySignedAffineIsometry s (productKeyInwardReferencePoint s)
  have ht (j : Fin 3) : inner ℝ (productKeyTangent s j) (x-productKeyCenter s) = 0 := by
    rw [product_key_signed_pose_tangent_coordinate]
    simp [productKeyInwardReferencePoint,castSucc_ne_three j]
  have hn : inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) = -productKeyRho/2 := by
    rw [product_key_signed_pose_outward_coordinate]
    cases hs : s.2.2 <;> simp [productKeyInwardReferencePoint,productKeySign,hs] <;> ring
  have hc : x ∈ interior (productKeyCollar s) := by
    apply product_key_strict_collar_subset_interior s
    constructor
    · intro j; rw [ht]; norm_num [productKeyEta]
    · rw [hn]; norm_num [productKeyRho]
  apply (polygon_product_key_body_interior_local_iff s x hc).mpr
  rw [hn]
  have hb := (abs_le.mp (product_key_height_amplitude s (x-productKeyCenter s))).1
  norm_num [productKeyEta,productKeyN,productKeyRho] at hb ⊢
  linarith

/-- Exact full signed-pose coincidence in a packing forces opposite recipe
polarities. Neither absolute-label equality nor contact recognition is an input. -/
theorem coincident_signed_poses_opposite_signs (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour)
    (hd : Disjoint (interior (f '' polygonProductKeyBody)) (interior (g '' polygonProductKeyBody)))
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
    have hi := f.toHomeomorph.isOpenMap.image_interior_subset polygonProductKeyBody
      ⟨_,product_key_inward_reference_mem_interior s,rfl⟩
    have hj := g.toHomeomorph.isOpenMap.image_interior_subset polygonProductKeyBody
      ⟨_,product_key_inward_reference_mem_interior t,rfl⟩
    rw [← hw] at hpoint
    have hpoint' : f (productKeySignedAffineIsometry s (productKeyInwardReferencePoint s)) =
        g (productKeySignedAffineIsometry t (productKeyInwardReferencePoint t)) := by
      simpa only [hw] using hpoint
    exact Set.disjoint_left.mp hd hi (hpoint'.symm ▸ hj)
  cases hs : s.2.2 <;> cases ht : t.2.2 <;> simp_all [productKeySign]

theorem product_key_normal_reflection_mem_collar (s : ProductKeySite) (w : EFour) :
    productKeyNormalReflection s w ∈ productKeyReferenceCollar ↔
      w ∈ productKeyReferenceCollar := by
  have ht (j : Fin 3) : productKeyNormalReflection s w j.castSucc = w j.castSucc := by
    rw [product_key_normal_reflection_coordinate]
    simp [castSucc_ne_three j]
  have hn : |productKeyNormalReflection s w 3| = |w 3| := by
    rw [product_key_normal_reflection_coordinate]
    cases hs : s.2.2 <;> simp [productKeySign,hs]
  simp only [productKeyReferenceCollar,mem_setOf_eq,ht,hn]

/-- Signed and unsigned actual frames give the same full closed collar. -/
theorem product_key_signed_pose_image_collar (s : ProductKeySite) :
    productKeySignedAffineIsometry s '' productKeyReferenceCollar = productKeyCollar s := by
  ext x
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨productKeyNormalReflection s w,(product_key_normal_reflection_mem_collar s w).mpr hw,rfl⟩
  · rintro ⟨w,hw,rfl⟩
    refine ⟨(productKeyNormalReflection s).symm w,?_,?_⟩
    · apply (product_key_normal_reflection_mem_collar s _).mp
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hw
    · rw [product_key_signed_pose_apply,LinearIsometryEquiv.apply_symm_apply]

theorem coincident_signed_poses_collars (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g) :
    f '' productKeyCollar s = g '' productKeyCollar t := by
  rw [← product_key_signed_pose_image_collar s,← product_key_signed_pose_image_collar t,
    Set.image_image,Set.image_image]
  exact congrArg (fun h : EFour ≃ᵢ EFour => h '' productKeyReferenceCollar) hp

end
end SpectreGeometry
