module

public import SpectreGeometry.PolygonProductKeyCreaseSectors
public import SpectreGeometry.LocalConeGerm

@[expose] public section


/-! The two flat strata of the actual zero-extended key graph: points outside
the asymmetric footprint and strictly active single side faces. Both produce
literal computed halfspace germs, including all displacement directions. -/
namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration ProductCreaseSectors
open scoped InnerProductSpace

theorem product_key_height_zero_of_nonpos_branch (u : ProductKeySite)
    (b : ProductKeySide) (x : EFour) (hb : productKeyBranchProfile u b x ≤ 0) :
    productKeyHeight u (x-productKeyCenter u) = 0 := by
  let F : Fin 3 → EFour → ℝ := fun i v =>
    min (1 + (productKeyPrime i false : ℝ) * inner ℝ (productKeyTangent u i) v / productKeyEta)
      (1 - (productKeyPrime i true : ℝ) * inner ℝ (productKeyTangent u i) v / productKeyEta)
  have he : finiteLowerEnvelope F (x-productKeyCenter u) ≤ 0 := by
    have hu := finiteLowerEnvelope_le F (x-productKeyCenter u) b.1
    rcases b with ⟨i,e⟩
    cases e
    · have hb' : 1 + (productKeyPrime i false : ℝ) *
          inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta ≤ 0 := by
        simpa [productKeyBranchProfile] using hb
      exact (hu.trans (min_le_left _ _)).trans hb'
    · have hb' : 1 - (productKeyPrime i true : ℝ) *
          inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta ≤ 0 := by
        have heq : productKeyBranchProfile u (i,true) x =
            1 - (productKeyPrime i true : ℝ) *
              inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta := by
          simp [productKeyBranchProfile]
          ring
        rw [heq] at hb
        exact hb
      exact (hu.trans (min_le_right _ _)).trans hb'
  change (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) *
    max 0 (finiteLowerEnvelope F (x-productKeyCenter u)) = 0
  rw [max_eq_left he,mul_zero]

theorem product_key_negative_branch_local_halfspace (u : ProductKeySite)
    (b : ProductKeySide) (x : EFour) (hx : x ∈ productKeyGraphWindow u)
    (hb : productKeyBranchProfile u b x < 0) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔
        inner ℝ (productKeyOutwardNormal u) (y-productKeyCenter u) ≤ 0 := by
  have hc : Continuous (productKeyBranchProfile u b) := by unfold productKeyBranchProfile; fun_prop
  refine ⟨interior (productKeyCollar u) ∩ {y | productKeyBranchProfile u b y < 0},
    isOpen_interior.inter (isOpen_lt hc continuous_const),
    ⟨product_key_graph_window_subset_interior_collar u hx,hb⟩,?_⟩
  intro y hy
  rw [polygon_product_key_body_local_outward_iff u y hy.1,
    product_key_height_zero_of_nonpos_branch u b y hy.2.le]

theorem product_key_strict_branch_local_halfspace (u : ProductKeySite)
    (b : ProductKeySide) (x : EFour) (hx : x ∈ productKeyGraphWindow u)
    (hb : 0 < productKeyBranchProfile u b x)
    (hstrict : ∀ c, c ≠ b → productKeyBranchProfile u b x < productKeyBranchProfile u c x) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔
        inner ℝ (productKeySideNormal u b) (y-productKeyCenter u) ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN := by
  have hc : Continuous (productKeyBranchProfile u b) := by unfold productKeyBranchProfile; fun_prop
  refine ⟨interior (productKeyCollar u) ∩
    ({y | 0 < productKeyBranchProfile u b y} ∩ minimalBranchNeighborhood u b),
    isOpen_interior.inter ((isOpen_lt continuous_const hc).inter
      (minimalBranchNeighborhood_isOpen u b)),
    ⟨product_key_graph_window_subset_interior_collar u hx,hb,
      fun c => hstrict c.val c.property⟩,?_⟩
  intro y hy
  rw [polygon_product_key_body_local_outward_iff u y hy.1,
    product_key_height_eq_side_height u b y
      ⟨hy.2.1.le,minimalBranchNeighborhood_minimal u b hy.2.2⟩]
  exact le_sideHeight_iff u b y

theorem localConeGerm_of_local_affine_halfspace (S U : Set EFour)
    (x n o : EFour) (c : ℝ) (hU : IsOpen U) (hxU : x ∈ U)
    (hplane : inner ℝ n (x-o) = c)
    (hgerm : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y-o) ≤ c) :
    LocalConeGerm S x {v | inner ℝ n v ≤ 0} := by
  refine ⟨(fun v : EFour => x+v) ⁻¹' U,
    hU.preimage (continuous_const.add continuous_id),by simpa using hxU,?_⟩
  intro v hv
  rw [hgerm (x+v) hv]
  simp only [mem_setOf_eq,add_sub_right_comm,inner_add_right,hplane]
  exact add_le_iff_nonpos_right c

theorem product_key_negative_branch_local_cone (u : ProductKeySite)
    (b : ProductKeySide) (x : EFour) (hx : x ∈ productKeyGraphWindow u)
    (hb : productKeyBranchProfile u b x < 0) :
    LocalConeGerm polygonProductKeyBody x
      {v | inner ℝ (productKeyOutwardNormal u) v ≤ 0} := by
  obtain ⟨U,hU,hxU,he⟩ := product_key_negative_branch_local_halfspace u b x hx hb
  apply localConeGerm_of_local_affine_halfspace _ U x _ (productKeyCenter u) 0 hU hxU _ he
  exact hx.1.trans (product_key_height_zero_of_nonpos_branch u b x hb.le)

theorem product_key_strict_branch_local_cone (u : ProductKeySite)
    (b : ProductKeySide) (x : EFour) (hx : x ∈ productKeyGraphWindow u)
    (hb : 0 < productKeyBranchProfile u b x)
    (hstrict : ∀ c, c ≠ b → productKeyBranchProfile u b x < productKeyBranchProfile u c x) :
    LocalConeGerm polygonProductKeyBody x {v | inner ℝ (productKeySideNormal u b) v ≤ 0} := by
  obtain ⟨U,hU,hxU,he⟩ := product_key_strict_branch_local_halfspace u b x hx hb hstrict
  apply localConeGerm_of_local_affine_halfspace _ U x _ (productKeyCenter u)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) hU hxU _ he
  apply product_key_side_face_plane u b x
  refine ⟨hx.1,hb.le,?_⟩
  intro c
  by_cases hcb : c = b
  · rw [hcb]
  · exact (hstrict c hcb).le

end
end SpectreGeometry
