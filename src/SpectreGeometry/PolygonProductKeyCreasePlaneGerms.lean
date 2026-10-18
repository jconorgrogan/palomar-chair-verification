module

public import SpectreGeometry.PolygonProductKeyGenericRidgeSectors

@[expose] public section


/-! Exact open two-plane germs of actual product-key creases. The reverse
inclusions reconstruct literal max-min graph membership from branch ordering. -/
namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration Set ProductCreaseSectors
open scoped InnerProductSpace
noncomputable section

theorem height_coefficient_ne_zero (u : ProductKeySite) :
    productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN ≠ 0 := by
  have hl : (productKeySignedLabel u : ℝ) ≠ 0 := by exact_mod_cast productKeySignedLabel_ne_zero u
  exact div_ne_zero (mul_ne_zero (by norm_num [productKeyEta]) hl) (by norm_num [productKeyN])

theorem baseCrease_iff_plane_intersection_on (u : ProductKeySite) (b : ProductKeySide)
    (y : EFour) (hy : y ∈ minimalBranchNeighborhood u b) :
    y ∈ baseCrease u b ↔ normalCoord u y = 0 ∧
      inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) =
        productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN := by
  constructor
  · intro h
    exact ⟨h.2,product_key_side_face_plane u b y h.1⟩
  · rintro ⟨hn,hp⟩
    have hh := (product_key_branch_normal_equation u b y).mpr hp
    change normalCoord u y = _ at hh
    rw [sideHeight_eq_scaled_branch,hn] at hh
    have hb : productKeyBranchProfile u b y = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left (height_coefficient_ne_zero u)
    have hall : ∀ c, 0 ≤ productKeyBranchProfile u c y := by
      intro c
      rw [← hb]
      exact minimalBranchNeighborhood_minimal u b hy c
    exact mem_baseCrease_of_branch_zero u b y hn hb hall

theorem baseGeneric_locally_eq_plane_intersection (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ baseCrease u b ↔ normalCoord u y = 0 ∧
        inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) =
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN := by
  refine ⟨minimalBranchNeighborhood u b,minimalBranchNeighborhood_isOpen u b,?_,
    fun y hy => baseCrease_iff_plane_intersection_on u b y hy⟩
  intro c
  rw [baseCrease_profile_zero u b hx.1]
  exact hx.2 c.val c.property

theorem sideCrease_iff_plane_intersection_on (u : ProductKeySite) (b c : ProductKeySide)
    (y : EFour) (hy : y ∈ pairBranchNeighborhood u b c) :
    y ∈ sideCrease u b c ↔
      (inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) =
        productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) ∧
      (inner ℝ (productKeySideNormal u c) (y-productKeyCenter u) =
        productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) := by
  constructor
  · intro h
    exact ⟨product_key_side_face_plane u b y h.1,product_key_side_face_plane u c y h.2⟩
  · rintro ⟨hb,hc⟩
    have hhb := (product_key_branch_normal_equation u b y).mpr hb
    have hhc := (product_key_branch_normal_equation u c y).mpr hc
    have heq : productKeyBranchProfile u b y = productKeyBranchProfile u c y := by
      have h := hhb.symm.trans hhc
      rw [sideHeight_eq_scaled_branch,sideHeight_eq_scaled_branch] at h
      exact mul_left_cancel₀ (height_coefficient_ne_zero u) h
    change 0 < min _ _ ∧ _ at hy
    rw [← heq,min_self] at hy
    have hmin : ∀ d, productKeyBranchProfile u b y ≤ productKeyBranchProfile u d y := by
      intro d
      by_cases hdb : d = b
      · rw [hdb]
      by_cases hdc : d = c
      · rw [hdc,heq]
      exact (hy.2 ⟨d,hdb,hdc⟩).le
    have hbr : y ∈ productKeyBranchRegion u b := ⟨hy.1.le,hmin⟩
    have hcr : y ∈ productKeyBranchRegion u c := by
      constructor
      · rw [← heq]; exact hy.1.le
      · intro d; rw [← heq]; exact hmin d
    have hg : y ∈ productKeyGraph u :=
      hhb.trans (product_key_height_eq_side_height u b y hbr).symm
    exact ⟨⟨hg,hbr⟩,⟨hg,hcr⟩⟩

theorem sideGeneric_locally_eq_plane_intersection (u : ProductKeySite) (b c : ProductKeySide)
    (x : EFour) (hx : x ∈ sideGeneric u b c) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ sideCrease u b c ↔
        (inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) =
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) ∧
        (inner ℝ (productKeySideNormal u c) (y-productKeyCenter u) =
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) := by
  refine ⟨pairBranchNeighborhood u b c,pairBranchNeighborhood_isOpen u b c,?_,
    fun y hy => sideCrease_iff_plane_intersection_on u b c y hy⟩
  change 0 < min _ _ ∧ _
  rw [← sideCrease_profile_equal u b c hx.1,min_self]
  exact ⟨hx.2.1,fun d => hx.2.2 d.val d.property.1 d.property.2⟩

end
end SpectreGeometry.ProductCrease
