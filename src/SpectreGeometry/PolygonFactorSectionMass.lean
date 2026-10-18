module

public import SpectreGeometry.PolygonProductNormalAngles
public import SpectreGeometry.NormalPlaneSectorMeasure
public import SpectreGeometry.PolygonBoundaryConeHalfplanes
public import PhysicalRegistration.PlanarSectorMeasure

@[expose] public section


/-! Actual angular measure of each literal native polygon boundary cone.
The measure is Haar angular measure on Real.Angle, applied to the actual
cosine/sine directions in the exact geometric cone. -/
namespace SpectreGeometry
noncomputable section
open Set MeasureTheory
open PhysicalRegistration.PlanarSectorMeasure

def factorConeDirections (right : Bool)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : BoundarySlot) : Set Real.Angle :=
  {θ | factorProjection right (L (PhysicalRegistration.PlanarSectorMeasure.direction θ)) ∈
    polygonBoundaryCone b}

def BoundaryNormalsIn (right : Bool)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : BoundarySlot) : Prop :=
  match b with
  | .inl i => factorNormal right (previous i) ∈ Set.range L ∧ factorNormal right i ∈ Set.range L
  | .inr i => factorNormal right i ∈ Set.range L

private theorem neg_normal_in {right : Bool}
    {L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour} {i : Fin 14}
    (h : factorNormal right i ∈ Set.range L) : -factorNormal right i ∈ Set.range L :=
  (LinearMap.range L.toLinearMap).neg_mem h

theorem factor_halfplane_mem_iff (right : Bool)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (i : Fin 14) (θ : Real.Angle) :
    θ ∈ sectorHalfplane L (-factorNormal right i) ↔
      0 ≤ RealPoint.det (realEdge i)
        (factorProjection right (L (PhysicalRegistration.PlanarSectorMeasure.direction θ))) := by
  simp only [sectorHalfplane,Set.mem_setOf_eq,inner_neg_left,factorNormal_inner_vector,neg_nonpos]

variable (right : Bool) (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)

private theorem factor_normal_angle_lt_pi (i : Fin 14) :
    InnerProductGeometry.angle (-factorNormal right (previous i))
      (-factorNormal right i) < Real.pi := by
  rw [InnerProductGeometry.angle_neg_neg,factorNormal_adjacent_angle]
  rcases native_adjacent_normal_angle_values i with h | h | h <;>
    rw [h] <;> linarith [Real.pi_pos]

private theorem factor_directions_edge (i : Fin 14) :
    factorConeDirections right L (.inr i) = sectorHalfplane L (-factorNormal right i) := by
  ext θ
  exact (factor_halfplane_mem_iff right L i θ).symm

private theorem factor_directions_inter (i : Fin 14)
    (hi : 0 < RealPoint.det (realEdge (previous i)) (realEdge i)) :
    factorConeDirections right L (.inl i) =
      sectorHalfplane L (-factorNormal right (previous i)) ∩
        sectorHalfplane L (-factorNormal right i) := by
  ext θ
  simp only [factorConeDirections,polygonBoundaryCone,Set.mem_setOf_eq,
    polygonVertexCone_eq_inter_of_pos i hi,Set.mem_inter_iff,factor_halfplane_mem_iff right L]

private theorem factor_directions_union (i : Fin 14)
    (hi : RealPoint.det (realEdge (previous i)) (realEdge i) < 0) :
    factorConeDirections right L (.inl i) =
      sectorHalfplane L (-factorNormal right (previous i)) ∪
        sectorHalfplane L (-factorNormal right i) := by
  ext θ
  simp only [factorConeDirections,polygonBoundaryCone,Set.mem_setOf_eq,
    polygonVertexCone_eq_union_of_neg i hi,Set.mem_union,factor_halfplane_mem_iff right L]

private theorem factor_directions_midpoint :
    factorConeDirections right L (.inl 10) = sectorHalfplane L (-factorNormal right 10) := by
  ext θ
  simp only [factorConeDirections,polygonBoundaryCone,Set.mem_setOf_eq,
    polygonVertexCone_eq_halfplane_of_edges_eq 10 real_midpoint_edges_eq,factor_halfplane_mem_iff right L]

/-- In any isometric two-plane containing the actual incident boundary normals,
the literal cone section of either polygon factor has positive π/6-integral mass. -/
theorem factor_boundary_cone_angular_mass (b : BoundarySlot) (hN : BoundaryNormalsIn right L b) :
    ∃ k : ℕ, 0 < k ∧ volume (factorConeDirections right L b) =
      ENNReal.ofReal ((k : ℝ) * (Real.pi / 6)) := by
  cases b with
  | inr i =>
      rw [factor_directions_edge,volume_sectorHalfplane L (neg_ne_zero.mpr (factorNormal_ne_zero right i)) (neg_normal_in hN)]
      refine ⟨6,by decide,?_⟩
      congr 1
      ring
  | inl i =>
      by_cases hi : i = 10
      · subst i
        rw [factor_directions_midpoint,volume_sectorHalfplane L (neg_ne_zero.mpr (factorNormal_ne_zero right 10)) (neg_normal_in hN.2)]
        refine ⟨6,by decide,?_⟩
        congr 1
        ring
      · have hdet := real_corner_det_ne_zero i hi
        rcases lt_or_gt_of_ne hdet with hneg | hpos
        · rw [factor_directions_union right L i hneg,
            volume_sectorHalfplane_union L (neg_ne_zero.mpr (factorNormal_ne_zero right (previous i)))
              (neg_ne_zero.mpr (factorNormal_ne_zero right i)) (neg_normal_in hN.1) (neg_normal_in hN.2) (factor_normal_angle_lt_pi right i),
            InnerProductGeometry.angle_neg_neg,factorNormal_adjacent_angle]
          rcases native_adjacent_normal_angle_values i with h | h | h
          · rw [h]
            refine ⟨9,by decide,?_⟩
            congr 1
            ring
          · rw [h]
            refine ⟨8,by decide,?_⟩
            congr 1
            ring
          · rw [h]
            refine ⟨6,by decide,?_⟩
            congr 1
            ring
        · rw [factor_directions_inter right L i hpos,
            volume_sectorHalfplane_inter L (neg_ne_zero.mpr (factorNormal_ne_zero right (previous i)))
              (neg_ne_zero.mpr (factorNormal_ne_zero right i)) (neg_normal_in hN.1) (neg_normal_in hN.2) (factor_normal_angle_lt_pi right i),
            InnerProductGeometry.angle_neg_neg,factorNormal_adjacent_angle]
          rcases native_adjacent_normal_angle_values i with h | h | h
          · rw [h]
            refine ⟨3,by decide,?_⟩
            congr 1
            ring
          · rw [h]
            refine ⟨4,by decide,?_⟩
            congr 1
            ring
          · rw [h]
            refine ⟨6,by decide,?_⟩
            congr 1
            ring

end
end SpectreGeometry
