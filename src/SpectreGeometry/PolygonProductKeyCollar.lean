module

public import SpectreGeometry.PolygonProductKeyCollarHalfplanes
public import SpectreGeometry.PolygonProductBoundaryGerm

@[expose] public section


/-! Admission of every concrete four-dimensional reference collar into the
actual raw P×P carrier. All bounds are the optimized recipe's stated bounds. -/
namespace SpectreGeometry
noncomputable section
open Set

def productKeyReferenceCollar : Set EFour :=
  {w | (∀ j : Fin 3, |w j.castSucc| ≤ 2 * productKeyEta) ∧ |w 3| ≤ productKeyRho}

def productKeyCollar (s : ProductKeySite) : Set EFour :=
  productKeyAffineIsometry s '' productKeyReferenceCollar

theorem product_key_affine_coordinates_left (i : Fin 14) (e : Bool) (w : EFour) :
    productKeyAffineIsometry (0,i,e) w =
      productCoordinates (productKeyActivePoint (0,i,e) (w 0) (w 3),
        (1/2 + w 1,1/2 + w 2)) := by
  rw [productKeyAffineIsometry_apply]
  ext j
  fin_cases j <;>
    simp [Fin.sum_univ_succ,productKeyFrame,productKeyTangent,productKeyOutwardNormal,
      productKeyCenter,productKeyActivePoint,productKeyPlanarOutward,
      leftNormalMap,rightNormalMap,productCoordinates,productCoordinateLinearEquiv] <;> ring

theorem product_key_affine_coordinates_right (i : Fin 14) (e : Bool) (w : EFour) :
    productKeyAffineIsometry (1,i,e) w =
      productCoordinates ((1/2 + w 1,1/2 + w 2),
        productKeyActivePoint (1,i,e) (w 0) (w 3)) := by
  rw [productKeyAffineIsometry_apply]
  ext j
  fin_cases j <;>
    simp [Fin.sum_univ_succ,productKeyFrame,productKeyTangent,productKeyOutwardNormal,
      productKeyCenter,productKeyActivePoint,productKeyPlanarOutward,
      leftNormalMap,rightNormalMap,productCoordinates,productCoordinateLinearEquiv] <;> ring

private theorem coordinates_body_mem (a b : RealPoint) :
    productCoordinates (a,b) ∈ polygonProductBody ↔ a ∈ polygonBody ∧ b ∈ polygonBody := by
  rw [polygon_product_body_mem]
  rfl

/-- The entire closed recipe collar, including its outer faces, has exactly
the raw carrier's expected normal-coordinate halfspace. -/
theorem product_key_reference_collar_carrier (s : ProductKeySite) (w : EFour)
    (hw : w ∈ productKeyReferenceCollar) :
    (productKeyAffineIsometry s w ∈ polygonProductBody ↔ w 3 ≤ 0) ∧
    (productKeyAffineIsometry s w ∈ interior polygonProductBody ↔ w 3 < 0) := by
  have h0 : |w 0| ≤ 2 * productKeyEta := hw.1 0
  have h1 : |w 1| ≤ 2 * productKeyEta := hw.1 1
  have h2 : |w 2| ≤ 2 * productKeyEta := hw.1 2
  have h3 : |w 3| ≤ productKeyRho := hw.2
  have hp := product_key_passive_square_interior (w 1) (w 2) h1 h2
  have hpc := interior_subset hp
  rcases s with ⟨b,i,e⟩
  fin_cases b
  · change ((productKeyAffineIsometry (0,i,e)) w ∈ polygonProductBody ↔ w 3 ≤ 0) ∧
      ((productKeyAffineIsometry (0,i,e)) w ∈ interior polygonProductBody ↔ w 3 < 0)
    have ha := product_key_active_collar_halfplane (0,i,e) (w 0) (w 3) h0 h3
    rw [product_key_affine_coordinates_left,coordinates_body_mem,productCoordinates_mem_interior]
    exact ⟨by simpa only [hpc,and_true] using ha.1,by simpa only [hp,and_true] using ha.2⟩
  · change ((productKeyAffineIsometry (1,i,e)) w ∈ polygonProductBody ↔ w 3 ≤ 0) ∧
      ((productKeyAffineIsometry (1,i,e)) w ∈ interior polygonProductBody ↔ w 3 < 0)
    have ha := product_key_active_collar_halfplane (1,i,e) (w 0) (w 3) h0 h3
    rw [product_key_affine_coordinates_right,coordinates_body_mem,productCoordinates_mem_interior]
    exact ⟨by simpa only [hpc,true_and] using ha.1,by simpa only [hp,true_and] using ha.2⟩

theorem product_key_collar_carrier (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyCollar s) :
    (x ∈ polygonProductBody ↔ (productKeyAffineIsometry s).symm x 3 ≤ 0) ∧
    (x ∈ interior polygonProductBody ↔ (productKeyAffineIsometry s).symm x 3 < 0) := by
  obtain ⟨w,hw,rfl⟩ := hx
  simpa only [AffineIsometryEquiv.symm_apply_apply] using product_key_reference_collar_carrier s w hw

theorem product_key_center_raw_boundary (s : ProductKeySite) :
    productKeyCenter s ∈ polygonProductBody ∧ productKeyCenter s ∉ interior polygonProductBody := by
  have hz : (0 : EFour) ∈ productKeyReferenceCollar := by
    constructor
    · intro j; norm_num [productKeyEta]
    · norm_num [productKeyRho]
  have h := product_key_reference_collar_carrier s 0 hz
  rw [productKeyAffineIsometry_zero] at h
  exact ⟨h.1.mpr (by simp),fun hi => by simpa using h.2.mp hi⟩

end
end SpectreGeometry
