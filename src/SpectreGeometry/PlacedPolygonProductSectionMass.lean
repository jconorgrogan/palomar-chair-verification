module

public import SpectreGeometry.PolygonProductBoundaryGerm

@[expose] public section


/-! Exact angular mass for the actual displacement cones of arbitrary
isometric copies of P×P. The root-normal containment premise is explicit,
expressed after pulling the chart back by the placement's linear isometry. -/
namespace SpectreGeometry
noncomputable section
open Set MeasureTheory
open PhysicalRegistration.PlanarSectorMeasure

def pulledBackNormalChart (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) :
    EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour :=
  f.toRealLinearIsometryEquiv.symm.toLinearIsometry.comp L

def placedProductBoundaryDirections (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot) : Set Real.Angle :=
  {θ | L (PhysicalRegistration.PlanarSectorMeasure.direction θ) ∈ f.toRealLinearIsometryEquiv '' productBoundaryCone b}

theorem placed_product_boundary_directions_eq (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot) :
    placedProductBoundaryDirections f L b =
      productBoundaryDirections (pulledBackNormalChart f L) b := by
  ext θ
  constructor
  · rintro ⟨x,hx,he⟩
    change f.toRealLinearIsometryEquiv.symm (L (PhysicalRegistration.PlanarSectorMeasure.direction θ)) ∈ productBoundaryCone b
    rw [← he,f.toRealLinearIsometryEquiv.symm_apply_apply]
    exact hx
  · intro h
    exact ⟨f.toRealLinearIsometryEquiv.symm (L (PhysicalRegistration.PlanarSectorMeasure.direction θ)),h,
      f.toRealLinearIsometryEquiv.apply_symm_apply _⟩

theorem placed_product_boundary_section_angular_mass (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot)
    (hN : ProductBoundaryNormalsIn (pulledBackNormalChart f L) b) :
    ∃ k : ℕ, 0 < k ∧ volume (placedProductBoundaryDirections f L b) =
      ENNReal.ofReal ((k : ℝ) * (Real.pi / 6)) := by
  rw [placed_product_boundary_directions_eq]
  exact polygon_product_boundary_section_angular_mass (pulledBackNormalChart f L) b hN

/-- At every actual boundary point of an arbitrarily placed literal P×P,
there is a full-neighborhood cone whose section has the proved spectrum in
every chart containing its actual boundary normals. The premise describing
that containment is retained, not replaced by registration or homochirality. -/
theorem placed_polygon_product_boundary_cone_spectrum (f : EFour ≃ᵢ EFour) (y : EFour)
    (hy : y ∈ f '' polygonProductBody) (hnot : y ∉ interior (f '' polygonProductBody)) :
    ∃ b : ProductBoundarySlot,
      LocalConeGerm (f '' polygonProductBody) y
        (f.toRealLinearIsometryEquiv '' productBoundaryCone b) ∧
      ∀ L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour,
        ProductBoundaryNormalsIn (pulledBackNormalChart f L) b →
        ∃ k : ℕ, 0 < k ∧ volume (placedProductBoundaryDirections f L b) =
          ENNReal.ofReal ((k : ℝ) * (Real.pi / 6)) := by
  obtain ⟨b,hb⟩ := placed_polygon_product_boundary_local_cone f y hy hnot
  exact ⟨b,hb,fun L hN => placed_product_boundary_section_angular_mass f L b hN⟩

end
end SpectreGeometry
