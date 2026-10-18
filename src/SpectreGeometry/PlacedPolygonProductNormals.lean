module

public import SpectreGeometry.PlacedPolygonProductSectionMass

@[expose] public section


/-! Physical-coordinate form of the actual boundary-normal containment
premise. This interface imposes neither orientation nor factor preservation
on an ambient placement or on its root-normal chart. -/
namespace SpectreGeometry
noncomputable section
open Set MeasureTheory

def PlacedBoundaryNormalsIn (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (right : Bool) : BoundarySlot → Prop
  | .inl i => f.toRealLinearIsometryEquiv (factorNormal right (previous i)) ∈ Set.range L ∧
      f.toRealLinearIsometryEquiv (factorNormal right i) ∈ Set.range L
  | .inr i => f.toRealLinearIsometryEquiv (factorNormal right i) ∈ Set.range L

def PlacedProductBoundaryNormalsIn (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) : ProductBoundarySlot → Prop
  | .left a => PlacedBoundaryNormalsIn f L false a
  | .right b => PlacedBoundaryNormalsIn f L true b
  | .both a b => PlacedBoundaryNormalsIn f L false a ∧ PlacedBoundaryNormalsIn f L true b

theorem placed_normal_chart_mem_iff (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (n : EFour) :
    f.toRealLinearIsometryEquiv n ∈ Set.range L ↔ n ∈ Set.range (pulledBackNormalChart f L) := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    change f.toRealLinearIsometryEquiv.symm (L v) = n
    rw [hv,f.toRealLinearIsometryEquiv.symm_apply_apply]
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    change f.toRealLinearIsometryEquiv.symm (L v) = n at hv
    rw [← hv,f.toRealLinearIsometryEquiv.apply_symm_apply]

theorem placed_boundary_normals_iff (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (right : Bool) (b : BoundarySlot) :
    PlacedBoundaryNormalsIn f L right b ↔ BoundaryNormalsIn right (pulledBackNormalChart f L) b := by
  cases b <;> simp only [PlacedBoundaryNormalsIn,BoundaryNormalsIn,placed_normal_chart_mem_iff]

theorem placed_product_boundary_normals_iff (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot) :
    PlacedProductBoundaryNormalsIn f L b ↔
      ProductBoundaryNormalsIn (pulledBackNormalChart f L) b := by
  cases b <;> simp only [PlacedProductBoundaryNormalsIn,ProductBoundaryNormalsIn,placed_boundary_normals_iff]

/-- Every actual boundary-point cone of an arbitrary physical copy has the
proved π/6 spectrum in every isometric plane containing its actual placed
boundary normals. This is an exact physical-coordinate premise, still to be
supplied by a separate generic key-ridge incidence theorem. -/
theorem placed_polygon_product_boundary_spectrum (f : EFour ≃ᵢ EFour) (y : EFour)
    (hy : y ∈ f '' polygonProductBody) (hnot : y ∉ interior (f '' polygonProductBody)) :
    ∃ b : ProductBoundarySlot,
      LocalConeGerm (f '' polygonProductBody) y
        (f.toRealLinearIsometryEquiv '' productBoundaryCone b) ∧
      ∀ L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour,
        PlacedProductBoundaryNormalsIn f L b →
        ∃ k : ℕ, 0 < k ∧ volume (placedProductBoundaryDirections f L b) =
          ENNReal.ofReal ((k : ℝ) * (Real.pi / 6)) := by
  obtain ⟨b,hb,hmass⟩ := placed_polygon_product_boundary_cone_spectrum f y hy hnot
  exact ⟨b,hb,fun L hN => hmass L ((placed_product_boundary_normals_iff f L b).mp hN)⟩

end
end SpectreGeometry
