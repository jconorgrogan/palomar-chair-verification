module

public import SpectreGeometry.PolygonProductKeyWindowConeClassification
public import SpectreGeometry.PolygonProductKeyOrdinaryGerms
public import SpectreGeometry.PolygonProductBoundarySignCones

@[expose] public section


/-! Every actual incident tile at a point generic for a root crease has a
closed finite-sign cone with its computed angular class. All chart ranges
come from actual passing boundary planes, including ordinary raw facets. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set MeasureTheory FiniteConeFan
open scoped InnerProductSpace
local instance : DecidableEq EFour := Classical.decEq EFour

theorem facet_equation_mem_key_boundary_plane (f : EFour ≃ᵢ EFour)
    (x : EFour) (r : Bool) (i : Fin 14)
    (h : inner ℝ (placedFacetNormal f r i) x = placedFacetOffset f r i) :
    x ∈ f '' productKeyBoundaryPlane (.inl (r,i)) := by
  rw [image_product_key_boundary_plane_uncentered]
  simpa only [productKeyBoundaryPlaneNormal,productKeyBoundaryPlaneLevel,
    productKeyBoundaryPlaneCenter,placedFacetNormal,placedFacetOffset,zero_add,mem_setOf_eq] using h

theorem product_facet_normals_in_of_passing_planes (f : EFour ≃ᵢ EFour)
    (x : EFour) (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot)
    (hb : ProductFacetEquations f x b)
    (hr : ∀ k : ProductKeyBoundaryPlaneIndex, x ∈ f '' productKeyBoundaryPlane k →
      f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal k) ∈ Set.range L) :
    PlacedProductBoundaryNormalsIn f L b := by
  have hf (r : Bool) (a : BoundarySlot) (ha : BoundaryFacetEquations f x r a) :
      PlacedBoundaryNormalsIn f L r a := by
    cases a with
    | inl i =>
      exact ⟨hr (.inl (r,previous i)) (facet_equation_mem_key_boundary_plane f x r (previous i) ha.1),
        hr (.inl (r,i)) (facet_equation_mem_key_boundary_plane f x r i ha.2)⟩
    | inr i => exact hr (.inl (r,i)) (facet_equation_mem_key_boundary_plane f x r i ha)
  cases b with
  | left a => exact hf false a hb
  | right a => exact hf true a hb
  | both a b => exact ⟨hf false a hb.1,hf true b hb.2⟩

theorem ordinary_boundary_cone_model (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hx : x ∈ frontier (f '' polygonProductKeyBody))
    (hw : ∀ u, x ∉ f '' productKeyGraphWindow u)
    (hr : ∀ k : ProductKeyBoundaryPlaneIndex, x ∈ f '' productKeyBoundaryPlane k →
      f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal k) ∈ Set.range L) :
    ∃ M : ActualBoundaryConeModel f x L, ConeSectorClassification f x L M.cone := by
  obtain ⟨b,hg,hf,hm⟩ := placed_polygon_product_key_ordinary_cone_spectrum f x hx hw
  have hN := product_facet_normals_in_of_passing_planes f x L b hf hr
  let M : ActualBoundaryConeModel f x L := {
    cone := f.toRealLinearIsometryEquiv '' productBoundaryCone b
    normals := (productBoundaryNormals b).image f.toRealLinearIsometryEquiv
    closed := placed_productBoundaryCone_closed f b
    signs := placed_productBoundary_signDetermined f b
    normal_range := (placed_productBoundaryNormals_range_iff f L b).mpr hN
    germ := hg }
  obtain ⟨k,hk,hMass⟩ := hm L hN
  refine ⟨M,Or.inl ⟨k,hk,?_⟩⟩
  change (volume (placedProductBoundaryDirections f L b)).toReal = _
  rw [hMass,ENNReal.toReal_ofReal]
  exact mul_nonneg (Nat.cast_nonneg k) (by positivity)

/-- Pointwise classification for every actual boundary incident. The listed
normal premise refers only to actual affine planes through this point. -/
theorem incident_boundary_cone_model (f : EFour ≃ᵢ EFour) (x p q : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hL : LinearMap.range L.toLinearMap = Submodule.span ℝ {p,q})
    (hx : x ∈ frontier (f '' polygonProductKeyBody))
    (hr : ∀ k : ProductKeyBoundaryPlaneIndex, x ∈ f '' productKeyBoundaryPlane k →
      f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal k) ∈ Set.range L) :
    ∃ M : ActualBoundaryConeModel f x L, ConeSectorClassification f x L M.cone := by
  by_cases hw : ∃ u, f.symm x ∈ productKeyGraphWindow u
  · obtain ⟨u,hu⟩ := hw
    have hs := placed_key_window_stratum_of_boundary_normal_span f u x p q hu
      (by intro k hk
          have hn := hr k hk
          change _ ∈ LinearMap.range L.toLinearMap at hn
          rwa [hL] at hn)
    exact key_window_cone_model f x L u hu hs hr
  · apply ordinary_boundary_cone_model f x L hx _ hr
    intro u hu
    apply hw
    obtain ⟨y,hy,he⟩ := hu
    refine ⟨u,?_⟩
    rw [← he,f.symm_apply_apply]
    exact hy

end
end SpectreGeometry.ProductCrease
