module

public import SpectreGeometry.PolygonProductKeyFrames

@[expose] public section


/-! Actual signed reference poses. Tangent coordinates are unchanged and the
reference normal is multiplied by the recipe polarity. Thus the positive
reference pyramid can be placed at either a bump or a dent without assuming
any lattice-preserving property of ambient isometries. -/
namespace SpectreGeometry
noncomputable section
open scoped InnerProductSpace

def productKeyNormalReflection (s : ProductKeySite) : EFour ≃ₗᵢ[ℝ] EFour :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin 4 =>
    if j = 3 then
      if s.2.2 then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ
    else LinearIsometryEquiv.refl ℝ ℝ)

theorem product_key_normal_reflection_coordinate (s : ProductKeySite)
    (w : EFour) (j : Fin 4) :
    productKeyNormalReflection s w j =
      if j = 3 then productKeySign s * w j else w j := by
  by_cases hj : j = 3 <;> cases hs : s.2.2 <;>
    simp [productKeyNormalReflection, LinearIsometryEquiv.piLpCongrRight_apply,
      productKeySign, hj, hs]

def productKeySignedAffineIsometry (s : ProductKeySite) : EFour ≃ᵃⁱ[ℝ] EFour :=
  (productKeyNormalReflection s).toAffineIsometryEquiv.trans (productKeyAffineIsometry s)

theorem product_key_signed_pose_apply (s : ProductKeySite) (w : EFour) :
    productKeySignedAffineIsometry s w =
      productKeyAffineIsometry s (productKeyNormalReflection s w) := rfl

theorem product_key_signed_pose_zero (s : ProductKeySite) :
    productKeySignedAffineIsometry s 0 = productKeyCenter s := by
  rw [product_key_signed_pose_apply, map_zero, productKeyAffineIsometry_zero]

private theorem positive_frame_coordinate (s : ProductKeySite) (w : EFour) (j : Fin 4) :
    inner ℝ (productKeyFrame s j) (productKeyAffineIsometry s w - productKeyCenter s) =
      w j := by
  rw [productKeyAffineIsometry_apply, add_sub_cancel_left]
  simp [inner_sum, real_inner_smul_right, productKeyFrame_inner, mul_ite]

theorem product_key_signed_pose_tangent_coordinate (s : ProductKeySite)
    (w : EFour) (j : Fin 3) :
    inner ℝ (productKeyTangent s j)
      (productKeySignedAffineIsometry s w - productKeyCenter s) = w j.castSucc := by
  rw [product_key_signed_pose_apply, ← productKeyFrame_tangent s j,
    positive_frame_coordinate, product_key_normal_reflection_coordinate]
  have hj : j.castSucc ≠ (3 : Fin 4) := by
    intro h
    have he := congrArg Fin.val h
    have := j.isLt
    change j.val = 3 at he
    omega
  simp [hj]

theorem product_key_signed_pose_outward_coordinate (s : ProductKeySite) (w : EFour) :
    inner ℝ (productKeyOutwardNormal s)
      (productKeySignedAffineIsometry s w - productKeyCenter s) = productKeySign s * w 3 := by
  rw [product_key_signed_pose_apply, ← productKeyFrame_normal s,
    positive_frame_coordinate, product_key_normal_reflection_coordinate]
  simp

theorem product_key_signed_pose_normal_coordinate (s : ProductKeySite) (w : EFour) :
    inner ℝ (productKeySign s • productKeyOutwardNormal s)
      (productKeySignedAffineIsometry s w - productKeyCenter s) = w 3 := by
  rw [real_inner_smul_left, product_key_signed_pose_outward_coordinate]
  cases hs : s.2.2 <;> simp [productKeySign, hs]

theorem product_key_signed_inverse_tangent_coordinate (s : ProductKeySite)
    (x : EFour) (j : Fin 3) :
    inner ℝ (productKeyTangent s j) (x - productKeyCenter s) =
      (productKeySignedAffineIsometry s).symm x j.castSucc := by
  simpa only [AffineIsometryEquiv.apply_symm_apply] using
    product_key_signed_pose_tangent_coordinate s ((productKeySignedAffineIsometry s).symm x) j

theorem product_key_signed_inverse_normal_coordinate (s : ProductKeySite) (x : EFour) :
    inner ℝ (productKeySign s • productKeyOutwardNormal s) (x - productKeyCenter s) =
      (productKeySignedAffineIsometry s).symm x 3 := by
  simpa only [AffineIsometryEquiv.apply_symm_apply] using
    product_key_signed_pose_normal_coordinate s ((productKeySignedAffineIsometry s).symm x)

end
end SpectreGeometry
