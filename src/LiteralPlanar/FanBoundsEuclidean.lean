module

public import LiteralPlanar.FanBoundsReal
public import SpectreGeometry.UnitEdgeDirections
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section


/-! A genuine Euclidean Lipschitz bound for each literal fan displacement.
The domain is the explicit barycentric simplex; identifying its union with P,
pasting all tiles, and applying global inversion are subsequent obligations. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry
open scoped NNReal

def euclideanDomain (i : Fin 14) : Set EPlane :=
  {x | euclideanCoordinates.symm x ∈ sourceDomain i}

def normal (i : Fin 14) : EPlane := euclideanCoordinates (quarterTurn (realEdge i))

def residual (i : Fin 14) (x : EPlane) : EPlane :=
  Quintic.fanHeight Quintic.amplitude (alpha i (euclideanCoordinates.symm x))
    (beta i (euclideanCoordinates.symm x)) • normal i

theorem normal_norm (i : Fin 14) : ‖normal i‖ = 1 := by
  have hd : RealPoint.dot (quarterTurn (realEdge i)) (quarterTurn (realEdge i)) = 1 := by
    simpa only [quarterTurn, RealPoint.dot, neg_mul_neg, add_comm] using real_edges_unit_squared i
  have hn := coordinate_dot_norm_squared (normal i)
  simp only [normal, Homeomorph.symm_apply_apply] at hn
  rw [hd] at hn
  change (1 : ℝ) = ‖normal i‖ ^ 2 at hn
  nlinarith [norm_nonneg (normal i)]

/-- Actual metric bound, using EuclideanSpace rather than the product max norm. -/
theorem residual_lipschitz (i : Fin 14) :
    LipschitzOnWith (90 / 1024 : ℝ≥0) (residual i) (euclideanDomain i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let p : RealPoint := euclideanCoordinates.symm x
  let q : RealPoint := euclideanCoordinates.symm y
  have he : euclideanCoordinates.symm (x - y) = p - q :=
    coordinateLinearEquiv.symm.map_sub x y
  have hpq := coordinate_dot_norm_squared (x - y)
  rw [he, ←dist_eq_norm] at hpq
  have hb := fan_displacement_scalar_bound i p q (dist x y) hx hy dist_nonneg hpq
  change dist (_ • normal i) (_ • normal i) ≤ _
  rw [dist_eq_norm, ←sub_smul, norm_smul, Real.norm_eq_abs, normal_norm, mul_one]
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
  convert hb using 1 <;> norm_num [Quintic.amplitude, p, q]

end
end LiteralPlanar.FanBounds
