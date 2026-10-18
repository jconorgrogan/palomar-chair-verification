module

public import SpectreGeometry.PolygonProductKeyRawAgreement
public import SpectreGeometry.PolygonProductKeyBranches
public import SpectreGeometry.PolygonProductFacetIncidence

@[expose] public section


/-! Explicit finite supporting-plane inventory for the actual bounded keyed
P×P body. All normals are computed and nonzero. The inventory and its
arbitrary-isometry transport have no tiling, orientation or lattice premise. -/
namespace SpectreGeometry
noncomputable section
open Set
open scoped InnerProductSpace

private theorem product_facet_equations_some (f : EFour ≃ᵢ EFour) (x : EFour)
    (b : ProductBoundarySlot) (hb : ProductFacetEquations f x b) :
    ∃ right : Bool, ∃ i : Fin 14,
      inner ℝ (placedFacetNormal f right i) x = placedFacetOffset f right i := by
  cases b with
  | left a =>
    cases a with
    | inl i => exact ⟨false, i, hb.2⟩
    | inr i => exact ⟨false, i, hb⟩
  | right a =>
    cases a with
    | inl i => exact ⟨true, i, hb.2⟩
    | inr i => exact ⟨true, i, hb⟩
  | both a b =>
    cases a with
    | inl i => exact ⟨false, i, hb.1.2⟩
    | inr i => exact ⟨false, i, hb.1⟩

theorem polygon_product_frontier_facet (x : EFour)
    (hx : x ∈ frontier polygonProductBody) :
    ∃ right : Bool, ∃ i : Fin 14,
      inner ℝ (factorNormal right i) (x-productFacetBase right i) = 0 := by
  have hm : x ∈ polygonProductBody := polygon_product_body_isCompact.isClosed.frontier_subset hx
  have hi : (IsometryEquiv.refl EFour) '' polygonProductBody = polygonProductBody := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hy
      exact ⟨y,hy,rfl⟩
  have hnorm (v : EFour) : (IsometryEquiv.refl EFour).toRealLinearIsometryEquiv v = v := by
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]
    change v-0=v
    exact sub_zero v
  obtain ⟨b,_,hb⟩ := placed_polygon_product_boundary_facet_incidence
    (IsometryEquiv.refl EFour) x ⟨x,hm,rfl⟩
      (by rw [hi]; exact hx.2)
  obtain ⟨right,i,he⟩ := product_facet_equations_some (IsometryEquiv.refl EFour) x b hb
  refine ⟨right,i,?_⟩
  have he' : inner ℝ (factorNormal right i) x =
      inner ℝ (factorNormal right i) (productFacetBase right i) := by
    simp only [placedFacetOffset,placedFacetNormal,hnorm] at he
    exact he
  rw [inner_sub_right,he',sub_self]

abbrev ProductKeyBoundaryPlaneIndex :=
  (Bool × Fin 14) ⊕ (ProductKeySite × Option ProductKeySide)

def productKeyBoundaryPlaneNormal : ProductKeyBoundaryPlaneIndex → EFour
  | .inl (right,i) => factorNormal right i
  | .inr (s,none) => productKeyOutwardNormal s
  | .inr (s,some b) => productKeySideNormal s b

def productKeyBoundaryPlaneCenter : ProductKeyBoundaryPlaneIndex → EFour
  | .inl (right,i) => productFacetBase right i
  | .inr (s,_) => productKeyCenter s

def productKeyBoundaryPlaneLevel : ProductKeyBoundaryPlaneIndex → ℝ
  | .inl _ => 0
  | .inr (_,none) => 0
  | .inr (s,some _) => productKeyEta * (productKeySignedLabel s : ℝ) / productKeyN

def productKeyBoundaryPlane (b : ProductKeyBoundaryPlaneIndex) : Set EFour :=
  {x | inner ℝ (productKeyBoundaryPlaneNormal b) (x-productKeyBoundaryPlaneCenter b) =
    productKeyBoundaryPlaneLevel b}

theorem product_key_boundary_plane_normal_ne_zero (b : ProductKeyBoundaryPlaneIndex) :
    productKeyBoundaryPlaneNormal b ≠ 0 := by
  cases b with
  | inl ri => exact factorNormal_ne_zero ri.1 ri.2
  | inr sb =>
    rcases sb with ⟨s,b⟩
    cases b with
    | none =>
      intro h
      have hn := productKeyOutwardNormal_norm s
      change productKeyOutwardNormal s = 0 at h
      rw [h,norm_zero] at hn
      norm_num at hn
    | some b =>
      intro h
      have hi := product_key_side_normal_inner_outward s b
      change productKeySideNormal s b = 0 at h
      rw [h,inner_zero_left] at hi
      norm_num at hi

theorem polygon_product_key_frontier_subset_boundary_planes :
    frontier polygonProductKeyBody ⊆ ⋃ b : ProductKeyBoundaryPlaneIndex,
      productKeyBoundaryPlane b := by
  intro x hx
  rcases polygon_product_key_frontier_cover hx with hraw | hkey
  · obtain ⟨right,i,hi⟩ := polygon_product_frontier_facet x hraw
    exact mem_iUnion.mpr ⟨.inl (right,i),hi⟩
  · obtain ⟨s,hs⟩ := mem_iUnion.mp hkey
    rcases product_key_graph_affine_plane_cover s x hs.1 with hzero | ⟨b,hb⟩
    · exact mem_iUnion.mpr ⟨.inr (s,none),hzero⟩
    · exact mem_iUnion.mpr ⟨.inr (s,some b),hb⟩

theorem image_product_key_boundary_plane (f : EFour ≃ᵢ EFour)
    (b : ProductKeyBoundaryPlaneIndex) :
    f '' productKeyBoundaryPlane b =
      {y | inner ℝ (f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b))
        (y-f (productKeyBoundaryPlaneCenter b)) = productKeyBoundaryPlaneLevel b} := by
  have hmap (x : EFour) :
      inner ℝ (f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b))
        (f x-f (productKeyBoundaryPlaneCenter b)) =
        inner ℝ (productKeyBoundaryPlaneNormal b) (x-productKeyBoundaryPlaneCenter b) := by
    have hv : f.toRealLinearIsometryEquiv (x-productKeyBoundaryPlaneCenter b) =
        f x-f (productKeyBoundaryPlaneCenter b) := by
      rw [map_sub,IsometryEquiv.toRealLinearIsometryEquiv_apply,
        IsometryEquiv.toRealLinearIsometryEquiv_apply]
      abel
    rw [← hv]
    exact f.toRealLinearIsometryEquiv.inner_map_map _ _
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hmap x).trans hx
  · intro hy
    refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
    change inner ℝ (productKeyBoundaryPlaneNormal b)
      (f.symm y-productKeyBoundaryPlaneCenter b) = _
    rw [← hmap,f.apply_symm_apply]
    exact hy

theorem placed_polygon_product_key_frontier_subset_boundary_planes (f : EFour ≃ᵢ EFour) :
    frontier (f '' polygonProductKeyBody) ⊆
      ⋃ b : ProductKeyBoundaryPlaneIndex,
        {y | inner ℝ (f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b))
          (y-f (productKeyBoundaryPlaneCenter b)) = productKeyBoundaryPlaneLevel b} := by
  intro y hy
  change y ∈ frontier (f.toHomeomorph '' polygonProductKeyBody) at hy
  rw [← f.toHomeomorph.image_frontier] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨b,hb⟩ := mem_iUnion.mp (polygon_product_key_frontier_subset_boundary_planes hx)
  apply mem_iUnion.mpr
  refine ⟨b,?_⟩
  rw [← image_product_key_boundary_plane]
  exact ⟨x,hb,rfl⟩

end
end SpectreGeometry
