module

public import SpectreGeometry.PolygonProductKeyFrames
public import SpectreGeometry.KeyNormalTwelfthAngle

@[expose] public section


/-! Actual affine-branch normals of the optimized 56-key P-product recipe.
The normals use the concrete site frames, signed labels, six primes and N=4357.
Admission of these branches into the boundary of a tube-replacement body is
separate from the present exact angle calculation. -/
namespace SpectreGeometry
open scoped InnerProductSpace
open InnerProductGeometry KeyNormalTwelfthAngle
noncomputable section

abbrev ProductKeySide := Fin 3 × Bool

def productKeySideSlope (s : ProductKeySite) (b : ProductKeySide) : ℝ :=
  (productKeySignedLabel s : ℝ) * (if b.2 then -1 else 1) *
    (productKeyPrime b.1 b.2 : ℝ) / productKeyN

def productKeySideNormal (s : ProductKeySite) (b : ProductKeySide) : EFour :=
  productKeyOutwardNormal s - productKeySideSlope s b • productKeyTangent s b.1

def productKeySideHeight (s : ProductKeySite) (b : ProductKeySide) (x : EFour) : ℝ :=
  productKeyEta * (productKeySignedLabel s : ℝ) / productKeyN +
    productKeySideSlope s b * inner ℝ (productKeyTangent s b.1) (x - productKeyCenter s)

theorem product_key_branch_normal_equation (s : ProductKeySite) (b : ProductKeySide)
    (x : EFour) :
    inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) = productKeySideHeight s b x ↔
      inner ℝ (productKeySideNormal s b) (x - productKeyCenter s) =
        productKeyEta * (productKeySignedLabel s : ℝ) / productKeyN := by
  simp only [productKeySideNormal,productKeySideHeight,inner_sub_left,real_inner_smul_left]
  constructor <;> intro h <;> linarith

theorem product_key_side_slope_sq (s : ProductKeySite) (b : ProductKeySide) :
    0 < productKeySideSlope s b ^ 2 ∧ productKeySideSlope s b ^ 2 < 1 / 64 := by
  rcases s with ⟨f,i,sign⟩
  rcases b with ⟨j,side⟩
  fin_cases f <;> cases sign <;> fin_cases j <;> cases side <;>
    norm_num [productKeySideSlope,productKeySignedLabel,productKeySign,
      productKeyPrime,productKeyPrimePairs,productKeyN]

private theorem product_key_tangent_inner_outward (s : ProductKeySite) (j : Fin 3) :
    inner ℝ (productKeyTangent s j) (productKeyOutwardNormal s) = 0 := by
  rw [real_inner_comm]
  exact productKeyOutwardNormal_inner_tangent s j

theorem product_key_side_normal_inner_outward (s : ProductKeySite) (b : ProductKeySide) :
    inner ℝ (productKeySideNormal s b) (productKeyOutwardNormal s) = 1 := by
  simp [productKeySideNormal,inner_sub_left,real_inner_smul_left,
    product_key_tangent_inner_outward,real_inner_self_eq_norm_sq,productKeyOutwardNormal_norm]

theorem product_key_side_normal_inner_self (s : ProductKeySite) (b : ProductKeySide) :
    inner ℝ (productKeySideNormal s b) (productKeySideNormal s b) =
      1 + productKeySideSlope s b ^ 2 := by
  unfold productKeySideNormal
  rw [inner_sub_left,inner_sub_right,inner_sub_right]
  simp only [real_inner_smul_left,real_inner_smul_right,product_key_tangent_inner_outward,
    productKeyOutwardNormal_inner_tangent,mul_zero,sub_zero]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    productKeyOutwardNormal_norm,productKeyTangent_norm]
  ring

theorem product_key_distinct_side_normal_inner (s : ProductKeySite)
    (b c : ProductKeySide) (hbc : b.1 ≠ c.1) :
    inner ℝ (productKeySideNormal s b) (productKeySideNormal s c) = 1 := by
  simp [productKeySideNormal,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,product_key_tangent_inner_outward,
    productKeyOutwardNormal_inner_tangent,real_inner_self_eq_norm_sq,
    productKeyOutwardNormal_norm,productKeyTangent_inner,hbc]

theorem product_key_base_normal_angle (s : ProductKeySite) (b : ProductKeySide) :
    0 < angle (productKeySideNormal s b) (productKeyOutwardNormal s) ∧
      angle (productKeySideNormal s b) (productKeyOutwardNormal s) < Real.pi / 12 := by
  apply geometric_normal_angle_lt_pi_div_twelve _ _
    (by rw [product_key_side_normal_inner_outward]; norm_num)
  have hs := product_key_side_slope_sq s b
  have he : (inner ℝ (productKeySideNormal s b) (productKeyOutwardNormal s) /
      (‖productKeySideNormal s b‖ * ‖productKeyOutwardNormal s‖)) ^ 2 =
      1 / (1 + productKeySideSlope s b ^ 2) := by
    rw [div_pow,mul_pow,← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
      product_key_side_normal_inner_outward,product_key_side_normal_inner_self,
      real_inner_self_eq_norm_sq,productKeyOutwardNormal_norm]
    norm_num
  rw [he]
  have hd : 0 < 1 + productKeySideSlope s b ^ 2 := by positivity
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith

theorem product_key_side_normal_angle (s : ProductKeySite)
    (b c : ProductKeySide) (hbc : b.1 ≠ c.1) :
    0 < angle (productKeySideNormal s b) (productKeySideNormal s c) ∧
      angle (productKeySideNormal s b) (productKeySideNormal s c) < Real.pi / 12 := by
  apply geometric_normal_angle_lt_pi_div_twelve _ _
    (by rw [product_key_distinct_side_normal_inner s b c hbc]; norm_num)
  have hs := product_key_side_slope_sq s b
  have ht := product_key_side_slope_sq s c
  have he : (inner ℝ (productKeySideNormal s b) (productKeySideNormal s c) /
      (‖productKeySideNormal s b‖ * ‖productKeySideNormal s c‖)) ^ 2 =
      1 / ((1 + productKeySideSlope s b ^ 2) * (1 + productKeySideSlope s c ^ 2)) := by
    rw [div_pow,mul_pow,← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
      product_key_distinct_side_normal_inner s b c hbc,
      product_key_side_normal_inner_self,product_key_side_normal_inner_self]
    norm_num
  rw [he]
  have hd : 0 < (1 + productKeySideSlope s b ^ 2) * (1 + productKeySideSlope s c ^ 2) := by positivity
  have hprod : productKeySideSlope s b ^ 2 * productKeySideSlope s c ^ 2 < 1 / 4096 := by
    calc
      productKeySideSlope s b ^ 2 * productKeySideSlope s c ^ 2 <
          (1 / 64 : ℝ) * productKeySideSlope s c ^ 2 := mul_lt_mul_of_pos_right hs.2 ht.1
      _ < (1 / 64 : ℝ) * (1 / 64) := mul_lt_mul_of_pos_left ht.2 (by norm_num)
      _ = 1 / 4096 := by norm_num
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos hs.1 ht.1]

private theorem product_key_angle_map (f : EFour ≃ᵢ EFour) (v w : EFour) :
    angle (f.toRealLinearIsometryEquiv v) (f.toRealLinearIsometryEquiv w) = angle v w :=
  f.toRealLinearIsometryEquiv.toLinearIsometry.angle_map v w

theorem product_key_placed_base_normal_angle (s : ProductKeySite) (b : ProductKeySide)
    (f : EFour ≃ᵢ EFour) :
    0 < angle (f.toRealLinearIsometryEquiv (productKeySideNormal s b))
      (f.toRealLinearIsometryEquiv (productKeyOutwardNormal s)) ∧
    angle (f.toRealLinearIsometryEquiv (productKeySideNormal s b))
      (f.toRealLinearIsometryEquiv (productKeyOutwardNormal s)) < Real.pi / 12 := by
  rw [product_key_angle_map]
  exact product_key_base_normal_angle s b

theorem product_key_placed_side_normal_angle (s : ProductKeySite)
    (b c : ProductKeySide) (hbc : b.1 ≠ c.1) (f : EFour ≃ᵢ EFour) :
    0 < angle (f.toRealLinearIsometryEquiv (productKeySideNormal s b))
      (f.toRealLinearIsometryEquiv (productKeySideNormal s c)) ∧
    angle (f.toRealLinearIsometryEquiv (productKeySideNormal s b))
      (f.toRealLinearIsometryEquiv (productKeySideNormal s c)) < Real.pi / 12 := by
  rw [product_key_angle_map]
  exact product_key_side_normal_angle s b c hbc

end
end SpectreGeometry
