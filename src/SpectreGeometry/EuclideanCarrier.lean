module

public import SpectreGeometry.PolygonBody
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-! The concrete carrier as a compact subset of the standard Euclidean
plane, with nonempty interior and the fourteen actual unit edge lengths.
No physical tiling or aperiodicity assertion is made here. -/
namespace SpectreGeometry
noncomputable section

def euclideanCoordinates : RealPoint ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (Homeomorph.finTwoArrow (X := ℝ)).symm.trans (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm

@[simp] theorem euclideanCoordinates_zero (x : RealPoint) : euclideanCoordinates x 0 = x.1 := rfl
@[simp] theorem euclideanCoordinates_one (x : RealPoint) : euclideanCoordinates x 1 = x.2 := rfl

def euclideanBody : Set (EuclideanSpace ℝ (Fin 2)) := euclideanCoordinates '' polygonBody
def euclideanVertex (i : Fin 14) : EuclideanSpace ℝ (Fin 2) := euclideanCoordinates (realVertex i)

theorem euclideanBody_compact : IsCompact euclideanBody :=
  polygonBody_compact.image euclideanCoordinates.continuous

theorem euclideanBody_interior_nonempty : (interior euclideanBody).Nonempty := by
  rw [euclideanBody,←euclideanCoordinates.image_interior]
  exact polygonBody_interior_nonempty.image euclideanCoordinates

theorem euclideanCoordinates_dist_squared (x y : RealPoint) :
    dist (euclideanCoordinates x) (euclideanCoordinates y)^2 =
      RealPoint.dot (RealPoint.sub x y) (RealPoint.sub x y) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_succ,Real.dist_eq,RealPoint.dot,RealPoint.sub,pow_two]

theorem euclidean_edges_unit (i : Fin 14) : dist (euclideanVertex (next i)) (euclideanVertex i) = 1 := by
  have h : dist (euclideanVertex (next i)) (euclideanVertex i)^2 = 1 := by
    rw [euclideanVertex,euclideanVertex,euclideanCoordinates_dist_squared]
    exact real_edges_unit_squared i
  have hn := dist_nonneg (x := euclideanVertex (next i)) (y := euclideanVertex i)
  nlinarith

end
end SpectreGeometry
