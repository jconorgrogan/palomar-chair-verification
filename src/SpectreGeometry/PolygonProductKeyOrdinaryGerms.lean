module

public import SpectreGeometry.PolygonProductKeyRawAgreement
public import SpectreGeometry.PolygonProductFacetIncidence

@[expose] public section


/-! Actual ordinary strata of the bounded keyed product, including all collar
boundaries. An arbitrary placement and absence from its actual graph windows
suffice for raw cone and facet incidence. Only normal-chart containment remains
explicit in the already checked positive integral π/6 angular spectrum. -/
namespace SpectreGeometry
noncomputable section
open Set MeasureTheory

/-- Local cone models transfer across an exact open neighborhood equality. -/
theorem LocalConeGerm.congr_open {S T C : Set EFour} {x : EFour}
    (h : LocalConeGerm S x C) (U : Set EFour) (hU : IsOpen U) (hxU : x ∈ U)
    (he : ∀ y ∈ U, y ∈ T ↔ y ∈ S) : LocalConeGerm T x C := by
  obtain ⟨V,hV,h0V,hg⟩ := h
  refine ⟨V ∩ (fun v : EFour => x+v) ⁻¹' U,
    hV.inter (hU.preimage (continuous_const.add continuous_id)),
    ⟨h0V,by simpa using hxU⟩,?_⟩
  intro v hv
  exact (he (x+v) hv.2).trans (hg v hv.1)

private theorem isometry_mem_image (f : EFour ≃ᵢ EFour) (A : Set EFour) (x : EFour) :
    f x ∈ f '' A ↔ x ∈ A := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact (f.injective he) ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem placed_polygon_product_key_ordinary_neighborhood (f : EFour ≃ᵢ EFour)
    (x : EFour) (hx : x ∈ frontier (f '' polygonProductKeyBody))
    (hwindow : ∀ u, x ∉ f '' productKeyGraphWindow u) :
    x ∈ frontier (f '' polygonProductBody) ∧
      ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, y ∈ f '' polygonProductKeyBody ↔ y ∈ f '' polygonProductBody := by
  change x ∈ frontier (f.toHomeomorph '' polygonProductKeyBody) at hx
  rw [← f.toHomeomorph.image_frontier] at hx
  obtain ⟨z,hz,rfl⟩ := hx
  have hw : ∀ u, z ∉ productKeyGraphWindow u := fun u hu => hwindow u ⟨z,hu,rfl⟩
  have hraw := polygon_product_key_frontier_raw_of_no_window z hz hw
  obtain ⟨U,hU,hzU,he⟩ := polygon_product_key_frontier_raw_neighborhood z hz hw
  constructor
  · change f.toHomeomorph z ∈ frontier (f.toHomeomorph '' polygonProductBody)
    rw [← f.toHomeomorph.image_frontier]
    exact ⟨z,hraw,rfl⟩
  · refine ⟨f '' U,f.toHomeomorph.isOpenMap _ hU,⟨z,hzU,rfl⟩,?_⟩
    rintro y ⟨v,hv,rfl⟩
    rw [isometry_mem_image,isometry_mem_image]
    exact he v hv

theorem placed_polygon_product_key_ordinary_cone_spectrum (f : EFour ≃ᵢ EFour)
    (x : EFour) (hx : x ∈ frontier (f '' polygonProductKeyBody))
    (hwindow : ∀ u, x ∉ f '' productKeyGraphWindow u) :
    ∃ b : ProductBoundarySlot,
      LocalConeGerm (f '' polygonProductKeyBody) x
        (f.toRealLinearIsometryEquiv '' productBoundaryCone b) ∧
      ProductFacetEquations f x b ∧
      ∀ L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour,
        PlacedProductBoundaryNormalsIn f L b →
        ∃ k : ℕ, 0 < k ∧ volume (placedProductBoundaryDirections f L b) =
          ENNReal.ofReal ((k : ℝ) * (Real.pi / 6)) := by
  obtain ⟨hraw,U,hU,hxU,he⟩ := placed_polygon_product_key_ordinary_neighborhood f x hx hwindow
  have hm : x ∈ f '' polygonProductBody :=
    ((polygon_product_body_isCompact.image f.continuous).isClosed).frontier_subset hraw
  obtain ⟨b,hg,hfacets⟩ := placed_polygon_product_boundary_facet_incidence f x hm hraw.2
  refine ⟨b,hg.congr_open U hU hxU he,hfacets,?_⟩
  intro L hN
  exact placed_product_boundary_section_angular_mass f L b
    ((placed_product_boundary_normals_iff f L b).mp hN)

end
end SpectreGeometry
