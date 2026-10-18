module

public import SpectreGeometry.PolygonLocalConeGerms
public import SpectreGeometry.EuclideanCarrier
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section


/-! Actual local body cones for arbitrary isometric copies of the literal
four-dimensional product P×P. No angular mass or key recognition is asserted. -/
namespace SpectreGeometry
noncomputable section
open Set

abbrev EFour := EuclideanSpace ℝ (Fin 4)

def productCoordinateLinearEquiv : (RealPoint × RealPoint) ≃ₗ[ℝ] EFour where
  toFun x := WithLp.toLp 2 ![x.1.1,x.1.2,x.2.1,x.2.2]
  invFun y := ((y 0,y 1),(y 2,y 3))
  left_inv := by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  right_inv := by intro y; ext i; fin_cases i <;> rfl
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def productCoordinates : (RealPoint × RealPoint) ≃L[ℝ] EFour :=
  productCoordinateLinearEquiv.toContinuousLinearEquiv

def polygonProductBody : Set EFour :=
  productCoordinates '' (polygonBody ×ˢ polygonBody)

theorem polygon_product_body_mem (y : EFour) :
    y ∈ polygonProductBody ↔ (y 0,y 1) ∈ polygonBody ∧ (y 2,y 3) ∈ polygonBody := by
  change y ∈ productCoordinates '' (polygonBody ×ˢ polygonBody) ↔ _
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hy
    refine ⟨((y 0,y 1),(y 2,y 3)),hy,?_⟩
    exact productCoordinateLinearEquiv.apply_symm_apply y

/-- Native all-direction cone data for every product-carrier point. -/
theorem polygon_product_local_cone (x : RealPoint × RealPoint)
    (hx : x ∈ polygonBody ×ˢ polygonBody) :
    ∃ C D : Set RealPoint,
      LocalConeGerm polygonProductBody (productCoordinates x)
        (productCoordinates '' (C ×ˢ D)) ∧
      (C = Set.univ ∨ ∃ b : BoundarySlot, BoundarySlotAt b x.1 ∧ C = polygonBoundaryCone b) ∧
      (D = Set.univ ∨ ∃ b : BoundarySlot, BoundarySlotAt b x.2 ∧ D = polygonBoundaryCone b) := by
  obtain ⟨C,hC,hCshape⟩ := polygon_point_local_cone x.1 hx.1
  obtain ⟨D,hD,hDshape⟩ := polygon_point_local_cone x.2 hx.2
  exact ⟨C,D,(hC.prod hD).map_continuousLinearEquiv productCoordinates,hCshape,hDshape⟩

/-- Every actual product-carrier incidence has a literal transported cone.
The placement is an arbitrary Euclidean isometry; no properness, registration,
common splitting, or tiling premise is supplied. -/
theorem placed_polygon_product_local_cone (f : EFour ≃ᵢ EFour) (y : EFour)
    (hy : y ∈ f '' polygonProductBody) :
    ∃ (x : RealPoint × RealPoint) (C D : Set RealPoint),
      x ∈ polygonBody ×ˢ polygonBody ∧ y = f (productCoordinates x) ∧
      LocalConeGerm (f '' polygonProductBody) y
        (f.toRealLinearIsometryEquiv '' (productCoordinates '' (C ×ˢ D))) ∧
      (C = Set.univ ∨ ∃ b : BoundarySlot, BoundarySlotAt b x.1 ∧ C = polygonBoundaryCone b) ∧
      (D = Set.univ ∨ ∃ b : BoundarySlot, BoundarySlotAt b x.2 ∧ D = polygonBoundaryCone b) := by
  obtain ⟨z,hz,rfl⟩ := hy
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨C,D,hcone,hC,hD⟩ := polygon_product_local_cone x hx
  exact ⟨x,C,D,hx,rfl,hcone.map_isometryEquiv f,hC,hD⟩

end
end SpectreGeometry
