module

public import SpectreGeometry.PolygonFactorSectionMass
public import SpectreGeometry.PolygonProductNormalPlane

@[expose] public section


/-! Actual boundary-cone sections of the literal product P×P. A root-normal
plane is an arbitrary isometric two-plane containing the actual incident
boundary normals. Its containment premise remains explicit; it is not yet
inferred from any key or tiling incidence. -/
namespace SpectreGeometry
noncomputable section
open Set MeasureTheory
open PhysicalRegistration.PlanarSectorMeasure

inductive ProductBoundarySlot where
  | left (a : BoundarySlot)
  | right (b : BoundarySlot)
  | both (a b : BoundarySlot)

def productBoundaryCone : ProductBoundarySlot → Set EFour
  | .left a => productCoordinates '' (polygonBoundaryCone a ×ˢ Set.univ)
  | .right b => productCoordinates '' (Set.univ ×ˢ polygonBoundaryCone b)
  | .both a b => productCoordinates '' (polygonBoundaryCone a ×ˢ polygonBoundaryCone b)

def ProductBoundaryNormalsIn (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) :
    ProductBoundarySlot → Prop
  | .left a => BoundaryNormalsIn false L a
  | .right b => BoundaryNormalsIn true L b
  | .both a b => BoundaryNormalsIn false L a ∧ BoundaryNormalsIn true L b

def productBoundaryDirections (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (b : ProductBoundarySlot) : Set Real.Angle :=
  {θ | L (PhysicalRegistration.PlanarSectorMeasure.direction θ) ∈ productBoundaryCone b}

theorem product_coordinates_mem_image (C D : Set RealPoint) (v : EFour) :
    v ∈ productCoordinates '' (C ×ˢ D) ↔
      factorProjection false v ∈ C ∧ factorProjection true v ∈ D := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro h
    refine ⟨((v 0,v 1),(v 2,v 3)),h,?_⟩
    exact productCoordinateLinearEquiv.apply_symm_apply v

private def boundaryEnd : BoundarySlot → Fin 14
  | .inl i => i
  | .inr i => i

private def BoundaryFlat : BoundarySlot → Prop
  | .inl i => i = 10
  | .inr _ => True

private theorem end_normal_in (r : Bool) (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (b : BoundarySlot) (h : BoundaryNormalsIn r L b) :
    factorNormal r (boundaryEnd b) ∈ Set.range L := by
  cases b with
  | inl i => exact h.2
  | inr i => exact h

private theorem both_slots_flat (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (a b : BoundarySlot) (ha : BoundaryNormalsIn false L a) (hb : BoundaryNormalsIn true L b) :
    BoundaryFlat a ∧ BoundaryFlat b := by
  constructor
  · cases a with
    | inr i => trivial
    | inl i =>
        by_contra hi
        exact native_left_corner_excludes_right_normal L i (boundaryEnd b) hi
          ha.1 ha.2 (end_normal_in true L b hb)
  · cases b with
    | inr i => trivial
    | inl i =>
        by_contra hi
        exact native_right_corner_excludes_left_normal L i (boundaryEnd a) hi
          hb.1 hb.2 (end_normal_in false L a ha)

private theorem flat_factor_directions (r : Bool)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : BoundarySlot) (hb : BoundaryFlat b) :
    factorConeDirections r L b = sectorHalfplane L (-factorNormal r (boundaryEnd b)) := by
  cases b with
  | inr i =>
      ext θ
      exact (factor_halfplane_mem_iff r L i θ).symm
  | inl i =>
      change i = 10 at hb
      subst i
      ext θ
      simp only [factorConeDirections,polygonBoundaryCone,Set.mem_setOf_eq,boundaryEnd,
        polygonVertexCone_eq_halfplane_of_edges_eq 10 real_midpoint_edges_eq,
        factor_halfplane_mem_iff]

/-- The literal P×P boundary-cone section in any two-plane containing its
actual boundary normals has a positive π/6-integral angular mass. Neither
orientation nor factor preservation is required of the two-plane chart. -/
theorem polygon_product_boundary_section_angular_mass
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot)
    (hN : ProductBoundaryNormalsIn L b) :
    ∃ k : ℕ, 0 < k ∧ volume (productBoundaryDirections L b) =
      ENNReal.ofReal ((k : ℝ) * (Real.pi / 6)) := by
  cases b with
  | left a =>
      have he : productBoundaryDirections L (.left a) = factorConeDirections false L a := by
        ext θ
        simp only [productBoundaryDirections,productBoundaryCone,Set.mem_setOf_eq,
          product_coordinates_mem_image,factorConeDirections,Set.mem_univ,and_true,true_and,Set.mem_inter_iff]
      rw [he]
      exact factor_boundary_cone_angular_mass false L a hN
  | right b =>
      have he : productBoundaryDirections L (.right b) = factorConeDirections true L b := by
        ext θ
        simp only [productBoundaryDirections,productBoundaryCone,Set.mem_setOf_eq,
          product_coordinates_mem_image,factorConeDirections,Set.mem_univ,and_true,true_and,Set.mem_inter_iff]
      rw [he]
      exact factor_boundary_cone_angular_mass true L b hN
  | both a b =>
      obtain ⟨ha,hb⟩ := hN
      obtain ⟨hfa,hfb⟩ := both_slots_flat L a b ha hb
      have he : productBoundaryDirections L (.both a b) =
          factorConeDirections false L a ∩ factorConeDirections true L b := by
        ext θ
        simp only [productBoundaryDirections,productBoundaryCone,Set.mem_setOf_eq,
          product_coordinates_mem_image,factorConeDirections,Set.mem_univ,and_true,true_and,Set.mem_inter_iff]
      rw [he,flat_factor_directions false L a hfa,flat_factor_directions true L b hfb]
      have hn : -factorNormal false (boundaryEnd a) ∈ Set.range L :=
        (LinearMap.range L.toLinearMap).neg_mem (end_normal_in false L a ha)
      have hm : -factorNormal true (boundaryEnd b) ∈ Set.range L :=
        (LinearMap.range L.toLinearMap).neg_mem (end_normal_in true L b hb)
      have ho : inner ℝ (-factorNormal false (boundaryEnd a))
          (-factorNormal true (boundaryEnd b)) = 0 := by
        simp only [inner_neg_left,inner_neg_right,neg_neg]
        simpa [factorNormal] using
          native_product_normals_orthogonal (boundaryEnd a) (boundaryEnd b)
      rw [volume_sectorHalfplane_orthogonal L
        (neg_ne_zero.mpr (factorNormal_ne_zero false (boundaryEnd a)))
        (neg_ne_zero.mpr (factorNormal_ne_zero true (boundaryEnd b))) hn hm ho]
      refine ⟨3,by decide,?_⟩
      congr 1
      ring

end
end SpectreGeometry
