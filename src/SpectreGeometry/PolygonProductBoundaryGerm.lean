module

public import SpectreGeometry.PolygonProductSectionMass

@[expose] public section


/-! Every actual boundary point of the literal product carrier has one of
the three proved boundary-cone germs. Arbitrary ambient isometries transport
this full neighborhood statement by their actual linear displacement map.
No normal-plane containment or angular-mass hypothesis occurs here. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem productCoordinates_mem_interior (x : RealPoint × RealPoint) :
    productCoordinates x ∈ interior polygonProductBody ↔
      x.1 ∈ interior polygonBody ∧ x.2 ∈ interior polygonBody := by
  change productCoordinates.toHomeomorph x ∈
    interior (productCoordinates.toHomeomorph '' (polygonBody ×ˢ polygonBody)) ↔
      x.1 ∈ interior polygonBody ∧ x.2 ∈ interior polygonBody
  rw [← productCoordinates.toHomeomorph.image_interior, interior_prod_eq]
  constructor
  · rintro ⟨z,hz,he⟩
    have hzx : z = x := productCoordinates.injective he
    simpa only [hzx, Set.mem_prod] using hz
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- Body membership together with noninteriority supplies a genuine boundary
stratum and a full local cone germ, including retained straight midpoints. -/
theorem polygon_product_boundary_local_cone (x : RealPoint × RealPoint)
    (hx : x ∈ polygonBody ×ˢ polygonBody)
    (hnot : productCoordinates x ∉ interior polygonProductBody) :
    ∃ b : ProductBoundarySlot,
      LocalConeGerm polygonProductBody (productCoordinates x) (productBoundaryCone b) := by
  by_cases hleft : x.1 ∈ interior polygonBody
  · have hright : x.2 ∉ interior polygonBody := by
      intro hright
      exact hnot ((productCoordinates_mem_interior x).mpr ⟨hleft,hright⟩)
    obtain ⟨b,hb⟩ := frontier_has_slot x.2 ⟨subset_closure hx.2,hright⟩
    refine ⟨.right b,?_⟩
    exact ((polygon_interior_local_cone x.1 hleft).prod
      (polygon_boundary_local_cone b x.2 hb)).map_continuousLinearEquiv productCoordinates
  · obtain ⟨a,ha⟩ := frontier_has_slot x.1 ⟨subset_closure hx.1,hleft⟩
    by_cases hright : x.2 ∈ interior polygonBody
    · refine ⟨.left a,?_⟩
      exact ((polygon_boundary_local_cone a x.1 ha).prod
        (polygon_interior_local_cone x.2 hright)).map_continuousLinearEquiv productCoordinates
    · obtain ⟨b,hb⟩ := frontier_has_slot x.2 ⟨subset_closure hx.2,hright⟩
      refine ⟨.both a b,?_⟩
      exact ((polygon_boundary_local_cone a x.1 ha).prod
        (polygon_boundary_local_cone b x.2 hb)).map_continuousLinearEquiv productCoordinates

/-- The native boundary-cone classification at an actual boundary point of
an arbitrary isometric placement of the four-dimensional product carrier. -/
theorem placed_polygon_product_boundary_local_cone (f : EFour ≃ᵢ EFour) (y : EFour)
    (hy : y ∈ f '' polygonProductBody)
    (hnot : y ∉ interior (f '' polygonProductBody)) :
    ∃ b : ProductBoundarySlot,
      LocalConeGerm (f '' polygonProductBody) y
        (f.toRealLinearIsometryEquiv '' productBoundaryCone b) := by
  obtain ⟨z,hz,rfl⟩ := hy
  obtain ⟨x,hx,rfl⟩ := hz
  have hnative : productCoordinates x ∉ interior polygonProductBody := by
    intro hi
    apply hnot
    change f.toHomeomorph (productCoordinates x) ∈
      interior (f.toHomeomorph '' polygonProductBody)
    rw [← f.toHomeomorph.image_interior]
    exact ⟨productCoordinates x,hi,rfl⟩
  obtain ⟨b,hb⟩ := polygon_product_boundary_local_cone x hx hnative
  exact ⟨b,hb.map_isometryEquiv f⟩

end
end SpectreGeometry
