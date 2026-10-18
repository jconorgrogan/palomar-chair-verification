module

public import SpectreGeometry.PolygonBoundaryNormalRank
public import SpectreGeometry.EuclideanCarrier
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

@[expose] public section


/-! Actual unit boundary normals and their unoriented Euclidean angles.
These are angles between normal vectors, not material cone angles or angular
mass. The straight midpoint has normal angle zero. -/
namespace SpectreGeometry
noncomputable section

def nativeEuclideanEdgeNormal (i : Fin 14) : EuclideanSpace ℝ (Fin 2) :=
  euclideanCoordinates (nativeEdgeNormal i)

/-- Rotation by a quarter-turn preserves the actual Euclidean inner product. -/
theorem native_euclidean_normal_inner (i j : Fin 14) :
    inner ℝ (nativeEuclideanEdgeNormal i) (nativeEuclideanEdgeNormal j) =
      RealPoint.dot (realEdge i) (realEdge j) := by
  unfold nativeEuclideanEdgeNormal
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ, nativeEdgeNormal, RealPoint.dot, mul_comm, add_comm]

theorem native_euclidean_normal_norm (i : Fin 14) :
    ‖nativeEuclideanEdgeNormal i‖ = 1 := by
  have hsq : ‖nativeEuclideanEdgeNormal i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, native_euclidean_normal_inner, real_edges_unit_squared]
  have hn := norm_nonneg (nativeEuclideanEdgeNormal i)
  nlinarith

/-- The finite exact adjacent-dot certificate embeds as these real inner
products, without a new floating-point or angle enumeration. -/
theorem native_adjacent_normal_inner_values (i : Fin 14) :
    inner ℝ (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) = 0 ∨
    inner ℝ (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) = 1 / 2 ∨
    inner ℝ (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) = 1 := by
  rw [native_euclidean_normal_inner, ← realize_edge, ← realize_edge, realize_dot]
  have h := adjacent_dot_values (previous i)
  rw [next_previous] at h
  rcases h with h | h | h
  · exact Or.inl (by rw [h]; norm_num [Quad3.eval])
  · exact Or.inr (Or.inl (by rw [h]; norm_num [Quad3.eval]))
  · exact Or.inr (Or.inr (by rw [h]; norm_num [Quad3.eval]))

/-- Catalogue of genuine unoriented angles between the two incident inward
unit normals. It does not distinguish a convex material wedge from a reflex
material wedge having the same pair of normal lines. -/
theorem native_adjacent_normal_angle_values (i : Fin 14) :
    InnerProductGeometry.angle
      (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) = Real.pi / 2 ∨
    InnerProductGeometry.angle
      (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) = Real.pi / 3 ∨
    InnerProductGeometry.angle
      (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) = 0 := by
  have he : InnerProductGeometry.angle
      (nativeEuclideanEdgeNormal (previous i)) (nativeEuclideanEdgeNormal i) =
      Real.arccos (inner ℝ (nativeEuclideanEdgeNormal (previous i))
        (nativeEuclideanEdgeNormal i)) := by
    simp only [InnerProductGeometry.angle, native_euclidean_normal_norm, one_mul, div_one]
  rcases native_adjacent_normal_inner_values i with h | h | h
  · exact Or.inl (by rw [he, h, Real.arccos_zero])
  · refine Or.inr (Or.inl ?_)
    rw [he, h, ← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  · exact Or.inr (Or.inr (by rw [he, h, Real.arccos_one]))

theorem native_midpoint_normal_angle_zero :
    InnerProductGeometry.angle
      (nativeEuclideanEdgeNormal (previous 10)) (nativeEuclideanEdgeNormal 10) = 0 := by
  have hn : nativeEuclideanEdgeNormal 10 ≠ 0 := by
    intro hz
    have h := native_euclidean_normal_norm 10
    simp only [hz, norm_zero, zero_ne_one] at h
  have he : nativeEuclideanEdgeNormal (previous 10) = nativeEuclideanEdgeNormal 10 := by
    unfold nativeEuclideanEdgeNormal
    rw [native_midpoint_normals_eq]
  rw [he]
  exact InnerProductGeometry.angle_self hn

end
end SpectreGeometry
