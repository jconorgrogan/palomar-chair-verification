module

public import SpectreGeometry.PolygonProductKeyCreaseHull

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open Set ProductCrease
noncomputable section

theorem placed_actualWholeKey_eq_hull (u : ProductKeySite) (f : EFour ≃ᵢ EFour) :
    f '' actualWholeKey u = convexHull ℝ (f '' creaseComplex u) := by
  rw [←actualWholeKey_convexHull_crease]
  exact f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap.image_convexHull _

/-- Equality of actual whole crease complexes recovers the absolute key label
and complete signed reference pose under arbitrary Euclidean placements. -/
theorem coincident_actualCreases (s t : ProductKeySite) (g h : EFour ≃ᵢ EFour)
    (heq : g '' creaseComplex s = h '' creaseComplex t) :
    s.1 = t.1 ∧
      (productKeySignedAffineIsometry s).toIsometryEquiv.trans g =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans h := by
  apply coincident_actualWholeKeys s t g h
  rw [placed_actualWholeKey_eq_hull,placed_actualWholeKey_eq_hull,heq]

end
end SpectreGeometry.ProductKeyReference
