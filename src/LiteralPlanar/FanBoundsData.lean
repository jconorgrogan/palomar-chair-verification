module

public import SpectreGeometry.PolygonFanData

@[expose] public section


/-! Exact coarse margins for the literal polynomial fan deformation.
Their Euclidean-real interpretation and Lipschitz consequences are separate.
-/
namespace LiteralPlanar.FanBounds
open SpectreGeometry

/-- Each radial vector has physical squared length strictly below9. -/
theorem center_radius_squared_lt_nine : ∀ i : Fin 14,
    Quad3.positive (Quad3.sub (36,0)
      (ExactPoint.dot (ExactPoint.sub (vertex i) fanCenter)
        (ExactPoint.sub (vertex i) fanCenter))) := by decide

/-- Every physical oriented fan determinant is strictly above1/10. -/
theorem fan_determinant_gt_tenth : ∀ i : Fin 14,
    Quad3.positive (Quad3.sub
      (Quad3.mul (10,0) (ExactPoint.det (edge i)
        (ExactPoint.sub fanCenter (vertex i)))) (4,0)) := by decide

end LiteralPlanar.FanBounds
