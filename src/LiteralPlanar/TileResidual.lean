module

public import LiteralPlanar.FanCoordinates
public import LiteralPlanar.FanBoundsEuclidean

@[expose] public section


/-! A single well-defined residual on the original P body, with exact edge
values and uniform bounds on its actual closed fan pieces. No whole-plane
pasting or curved tiling conclusion is asserted in this module. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry
open scoped NNReal

/-- A deterministic choice is unnecessary: compatibility proves independence
of whichever closed fan contains the point. -/
def chosenFan (p : RealPoint) : Fin 14 := by
  classical
  exact if h : p ∈ polygonBody then (Set.mem_iUnion.mp h).choose else 0

theorem chosenFan_mem (p : RealPoint) (hp : p ∈ polygonBody) :
    p ∈ triangleBody (chosenFan p) := by
  simp only [chosenFan, dif_pos hp]
  exact (Set.mem_iUnion.mp hp).choose_spec

def tileResidual (x : EPlane) : EPlane :=
  residual (chosenFan (euclideanCoordinates.symm x)) x

theorem residual_eq_on_triangle_intersection (i j : Fin 14) (x : EPlane)
    (hi : euclideanCoordinates.symm x ∈ triangleBody i)
    (hj : euclideanCoordinates.symm x ∈ triangleBody j) : residual i x = residual j x := by
  by_cases h : i = j
  · rw [h]
  · unfold residual
    rw [fanHeight_zero_on_overlap i j h _ hi hj,
      fanHeight_zero_on_overlap j i (Ne.symm h) _ hj hi]
    simp

theorem tileResidual_on_fan (i : Fin 14) (x : EPlane)
    (hi : euclideanCoordinates.symm x ∈ triangleBody i) :
    tileResidual x = residual i x := by
  apply residual_eq_on_triangle_intersection
  · exact chosenFan_mem _ (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · exact hi

theorem euclideanDomain_eq_triangle_image (i : Fin 14) :
    euclideanDomain i = euclideanCoordinates '' triangleBody i := by
  ext x
  change (euclideanCoordinates.symm x ∈ sourceDomain i) ↔ _
  rw [sourceDomain_eq_triangleBody]
  constructor
  · intro hx
    exact ⟨euclideanCoordinates.symm x,hx,euclideanCoordinates.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using hy

theorem tileResidual_lipschitz_on_fan (i : Fin 14) :
    LipschitzOnWith (90 / 1024 : ℝ≥0) tileResidual
      (euclideanCoordinates '' triangleBody i) := by
  rw [←euclideanDomain_eq_triangle_image]
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxi : euclideanCoordinates.symm x ∈ triangleBody i := by
    simpa only [euclideanDomain, Set.mem_setOf_eq, sourceDomain_eq_triangleBody] using hx
  have hyi : euclideanCoordinates.symm y ∈ triangleBody i := by
    simpa only [euclideanDomain, Set.mem_setOf_eq, sourceDomain_eq_triangleBody] using hy
  rw [tileResidual_on_fan i x hxi, tileResidual_on_fan i y hyi]
  exact (residual_lipschitz i).dist_le_mul x hx y hy

theorem alpha_interpolate (i : Fin 14) (t : ℝ) :
    alpha i (interpolate (realVertex i) (realVertex (next i)) t) = 1 - t := by
  rw [←affineFan_outer i (1 - t) t (by ring), alpha_affineFan]

theorem beta_interpolate (i : Fin 14) (t : ℝ) :
    beta i (interpolate (realVertex i) (realVertex (next i)) t) = t := by
  rw [←affineFan_outer i (1 - t) t (by ring), beta_affineFan]

theorem tileResidual_on_edge (i : Fin 14) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    tileResidual (euclideanCoordinates
      (interpolate (realVertex i) (realVertex (next i)) t)) =
      Quintic.height Quintic.amplitude (t - 1 / 2) • normal i := by
  rw [tileResidual_on_fan i]
  · simp only [residual, Homeomorph.symm_apply_apply, alpha_interpolate, beta_interpolate]
    rw [Quintic.fanHeight_edge _ _ _ (by ring)]
  · rw [Homeomorph.symm_apply_apply]
    exact polygonEdge_mem_triangleBody i ⟨t,ht,ht',rfl⟩

theorem tileResidual_at_vertex (i : Fin 14) : tileResidual (euclideanVertex i) = 0 := by
  have h := tileResidual_on_edge i 0 (by norm_num) (by norm_num)
  have he : (0 : ℝ) - 1 / 2 = -1 / 2 := by ring
  rw [he, Quintic.height_left, zero_smul] at h
  simpa only [interpolate_zero, euclideanVertex] using h

end
end LiteralPlanar.FanBounds
