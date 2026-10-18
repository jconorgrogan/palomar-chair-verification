module

public import SpectreGeometry.PolygonProductKeyGenericRidges

@[expose] public section


/-! Discharging the sector-germ hypotheses from the dense actual ridge sets. -/
namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration Set
open scoped InnerProductSpace
noncomputable section

theorem baseCrease_profile_zero (u : ProductKeySite) (b : ProductKeySide)
    {x : EFour} (hx : x ∈ baseCrease u b) : productKeyBranchProfile u b x = 0 := by
  have hheight : normalCoord u x =
      (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) *
        productKeyBranchProfile u b x := by
    exact hx.1.1.trans ((product_key_height_eq_side_height u b x hx.1.2).trans
      (ProductCreaseSectors.sideHeight_eq_scaled_branch u b x))
  have hlabel : (productKeySignedLabel u : ℝ) ≠ 0 := by
    exact_mod_cast productKeySignedLabel_ne_zero u
  have hcoef : productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num [productKeyEta]) hlabel) (by norm_num [productKeyN])
  rw [hx.2] at hheight
  exact (mul_eq_zero.mp hheight.symm).resolve_left hcoef

theorem sideCrease_profile_equal (u : ProductKeySite) (b c : ProductKeySide)
    {x : EFour} (hx : x ∈ sideCrease u b c) :
    productKeyBranchProfile u b x = productKeyBranchProfile u c x :=
  le_antisymm (hx.1.2.2 c) (hx.2.2.2 b)

theorem baseGeneric_local_sector_pos (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b) (ha : 0 < (productKeySignedLabel u : ℝ)) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤ 0 ∨
        inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN :=
  ProductCreaseSectors.body_locally_eq_base_sector_pos u b x
    (sideFace_subset_graphWindow u b hx.1.1) (baseCrease_profile_zero u b hx.1) hx.2 ha

theorem baseGeneric_local_sector_neg (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b) (ha : (productKeySignedLabel u : ℝ) < 0) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤ 0 ∧
        inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN :=
  ProductCreaseSectors.body_locally_eq_base_sector_neg u b x
    (sideFace_subset_graphWindow u b hx.1.1) (baseCrease_profile_zero u b hx.1) hx.2 ha

theorem sideGeneric_local_sector_pos (u : ProductKeySite) (b c : ProductKeySide)
    (x : EFour) (hx : x ∈ sideGeneric u b c) (ha : 0 < (productKeySignedLabel u : ℝ)) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔
        inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN ∧
        inner ℝ (productKeySideNormal u c) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN :=
  ProductCreaseSectors.body_locally_eq_side_sector_pos u b c x
    (sideFace_subset_graphWindow u b hx.1.1) hx.2.1 (sideCrease_profile_equal u b c hx.1) hx.2.2 ha

theorem sideGeneric_local_sector_neg (u : ProductKeySite) (b c : ProductKeySide)
    (x : EFour) (hx : x ∈ sideGeneric u b c) (ha : (productKeySignedLabel u : ℝ) < 0) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔
        inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN ∨
        inner ℝ (productKeySideNormal u c) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN :=
  ProductCreaseSectors.body_locally_eq_side_sector_neg u b c x
    (sideFace_subset_graphWindow u b hx.1.1) hx.2.1 (sideCrease_profile_equal u b c hx.1) hx.2.2 ha

end
end SpectreGeometry.ProductCrease
