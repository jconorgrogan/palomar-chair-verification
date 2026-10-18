module

public import SpectreGeometry.PlacedPolygonProductNormals

@[expose] public section


/-! The actual 28 ambient facet hyperplanes of each physical P×P copy.
Boundary strata retain their point incidence, and all normals used in the
cone-spectrum premise are normals to hyperplanes through that actual point. -/
namespace SpectreGeometry
noncomputable section
open Set

def productFacetBase (right : Bool) (i : Fin 14) : EFour :=
  if right then productCoordinates (0,realVertex i) else productCoordinates (realVertex i,0)

def placedFacetNormal (f : EFour ≃ᵢ EFour) (right : Bool) (i : Fin 14) : EFour :=
  f.toRealLinearIsometryEquiv (factorNormal right i)

def placedFacetOffset (f : EFour ≃ᵢ EFour) (right : Bool) (i : Fin 14) : ℝ :=
  inner ℝ (placedFacetNormal f right i) (f (productFacetBase right i))

private theorem productFacetBase_projection (right : Bool) (i : Fin 14) :
    factorProjection right (productFacetBase right i) = realVertex i := by
  cases right <;> rfl

theorem native_facet_equation_of_side_zero (right : Bool) (i : Fin 14) (z : EFour)
    (hz : side (realVertex i) (realVertex (next i)) (factorProjection right z) = 0) :
    inner ℝ (factorNormal right i) z =
      inner ℝ (factorNormal right i) (productFacetBase right i) := by
  rw [factorNormal_inner_vector,factorNormal_inner_vector,productFacetBase_projection]
  have he : RealPoint.det (realEdge i) (factorProjection right z) -
      RealPoint.det (realEdge i) (realVertex i) =
      side (realVertex i) (realVertex (next i)) (factorProjection right z) := by
    simp only [realEdge,side,RealPoint.det,RealPoint.sub]
    ring
  rw [hz] at he
  linarith

theorem placed_facet_equation_of_side_zero (f : EFour ≃ᵢ EFour)
    (right : Bool) (i : Fin 14) (z : EFour)
    (hz : side (realVertex i) (realVertex (next i)) (factorProjection right z) = 0) :
    inner ℝ (placedFacetNormal f right i) (f z) = placedFacetOffset f right i := by
  have hn := native_facet_equation_of_side_zero right i z hz
  have he (v : EFour) : f v = f.toRealLinearIsometryEquiv v + f 0 := by
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]
    abel
  unfold placedFacetOffset placedFacetNormal
  rw [he z,he (productFacetBase right i),inner_add_right,inner_add_right,
    f.toRealLinearIsometryEquiv.inner_map_map,f.toRealLinearIsometryEquiv.inner_map_map,hn]

def BoundaryFacetEquations (f : EFour ≃ᵢ EFour) (y : EFour) (right : Bool) : BoundarySlot → Prop
  | .inl i => inner ℝ (placedFacetNormal f right (previous i)) y = placedFacetOffset f right (previous i) ∧
      inner ℝ (placedFacetNormal f right i) y = placedFacetOffset f right i
  | .inr i => inner ℝ (placedFacetNormal f right i) y = placedFacetOffset f right i

def ProductFacetEquations (f : EFour ≃ᵢ EFour) (y : EFour) : ProductBoundarySlot → Prop
  | .left a => BoundaryFacetEquations f y false a
  | .right b => BoundaryFacetEquations f y true b
  | .both a b => BoundaryFacetEquations f y false a ∧ BoundaryFacetEquations f y true b

theorem boundary_slot_facet_equations (f : EFour ≃ᵢ EFour) (right : Bool)
    (z : EFour) (b : BoundarySlot) (hb : BoundarySlotAt b (factorProjection right z)) :
    BoundaryFacetEquations f (f z) right b := by
  cases b with
  | inl i =>
      change factorProjection right z = realVertex i at hb
      constructor
      · apply placed_facet_equation_of_side_zero
        rw [hb,next_previous]
        exact side_self_right _ _
      · apply placed_facet_equation_of_side_zero
        rw [hb]
        exact side_self_left _ _
  | inr i =>
      obtain ⟨t,ht,ht',he⟩ := hb
      apply placed_facet_equation_of_side_zero
      rw [he]
      exact det_interpolate_self _ _ _

def ProductBoundarySlotAt : ProductBoundarySlot → RealPoint × RealPoint → Prop
  | .left a,x => BoundarySlotAt a x.1 ∧ x.2 ∈ interior polygonBody
  | .right b,x => x.1 ∈ interior polygonBody ∧ BoundarySlotAt b x.2
  | .both a b,x => BoundarySlotAt a x.1 ∧ BoundarySlotAt b x.2

theorem polygon_product_boundary_has_slot (x : RealPoint × RealPoint)
    (hx : x ∈ polygonBody ×ˢ polygonBody)
    (hnot : productCoordinates x ∉ interior polygonProductBody) :
    ∃ b : ProductBoundarySlot, ProductBoundarySlotAt b x := by
  by_cases hl : x.1 ∈ interior polygonBody
  · have hr : x.2 ∉ interior polygonBody := fun h =>
      hnot ((productCoordinates_mem_interior x).mpr ⟨hl,h⟩)
    obtain ⟨b,hb⟩ := frontier_has_slot x.2 ⟨subset_closure hx.2,hr⟩
    exact ⟨.right b,hl,hb⟩
  · obtain ⟨a,ha⟩ := frontier_has_slot x.1 ⟨subset_closure hx.1,hl⟩
    by_cases hr : x.2 ∈ interior polygonBody
    · exact ⟨.left a,ha,hr⟩
    · obtain ⟨b,hb⟩ := frontier_has_slot x.2 ⟨subset_closure hx.2,hr⟩
      exact ⟨.both a b,ha,hb⟩

theorem ProductBoundarySlotAt.local_cone {b : ProductBoundarySlot} {x : RealPoint × RealPoint}
    (hb : ProductBoundarySlotAt b x) :
    LocalConeGerm polygonProductBody (productCoordinates x) (productBoundaryCone b) := by
  cases b with
  | left a => exact ((polygon_boundary_local_cone a x.1 hb.1).prod
      (polygon_interior_local_cone x.2 hb.2)).map_continuousLinearEquiv productCoordinates
  | right b => exact ((polygon_interior_local_cone x.1 hb.1).prod
      (polygon_boundary_local_cone b x.2 hb.2)).map_continuousLinearEquiv productCoordinates
  | both a b => exact ((polygon_boundary_local_cone a x.1 hb.1).prod
      (polygon_boundary_local_cone b x.2 hb.2)).map_continuousLinearEquiv productCoordinates

theorem ProductBoundarySlotAt.facet_equations {b : ProductBoundarySlot} {x : RealPoint × RealPoint}
    (hb : ProductBoundarySlotAt b x) (f : EFour ≃ᵢ EFour) :
    ProductFacetEquations f (f (productCoordinates x)) b := by
  cases b with
  | left a => exact boundary_slot_facet_equations f false (productCoordinates x) a hb.1
  | right b => exact boundary_slot_facet_equations f true (productCoordinates x) b hb.2
  | both a b => exact ⟨boundary_slot_facet_equations f false (productCoordinates x) a hb.1,
      boundary_slot_facet_equations f true (productCoordinates x) b hb.2⟩

/-- Each actual boundary point has a single literal cone model whose active
normals are exactly bound to physical facet hyperplanes passing through it. -/
theorem placed_polygon_product_boundary_facet_incidence (f : EFour ≃ᵢ EFour) (y : EFour)
    (hy : y ∈ f '' polygonProductBody) (hnot : y ∉ interior (f '' polygonProductBody)) :
    ∃ b : ProductBoundarySlot,
      LocalConeGerm (f '' polygonProductBody) y
        (f.toRealLinearIsometryEquiv '' productBoundaryCone b) ∧ ProductFacetEquations f y b := by
  obtain ⟨z,hz,rfl⟩ := hy
  obtain ⟨x,hx,rfl⟩ := hz
  have hn : productCoordinates x ∉ interior polygonProductBody := by
    intro hi
    apply hnot
    change f.toHomeomorph (productCoordinates x) ∈ interior (f.toHomeomorph '' polygonProductBody)
    rw [← f.toHomeomorph.image_interior]
    exact ⟨productCoordinates x,hi,rfl⟩
  obtain ⟨b,hb⟩ := polygon_product_boundary_has_slot x hx hn
  exact ⟨b,hb.local_cone.map_isometryEquiv f,hb.facet_equations f⟩

end
end SpectreGeometry
