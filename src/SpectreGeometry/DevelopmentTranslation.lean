module

public import SpectreGeometry.DevelopedRealCoordinates

@[expose] public section


/-! Equal physical displacements between registered points have equal
developed displacements. This is the algebraic part of period transport;
a homeomorphism and translation-invariant triangulation are still needed. -/
namespace SpectreGeometry
noncomputable section

theorem registered_development_displacement (root : EPlane ≃ᵢ EPlane)
    (x y z w : EPlane)
    (hx : sourcePoint root x ∈ quadraticPlane) (hy : sourcePoint root y ∈ quadraticPlane)
    (hz : sourcePoint root z ∈ quadraticPlane) (hw : sourcePoint root w ∈ quadraticPlane)
    (h : y-x = w-z) :
    physicalVertexDevelopment root y-physicalVertexDevelopment root x =
      physicalVertexDevelopment root w-physicalVertexDevelopment root z := by
  rw [physicalVertexDevelopment_registered root x hx,physicalVertexDevelopment_registered root y hy,
    physicalVertexDevelopment_registered root z hz,physicalVertexDevelopment_registered root w hw,
    ←kiteCoordinateEmbedding_sub,←kiteCoordinateEmbedding_sub,←map_sub,←map_sub]
  congr 2
  apply Subtype.ext
  change sourcePoint root y-sourcePoint root x = sourcePoint root w-sourcePoint root z
  change euclideanCoordinates.symm (root.symm y)-euclideanCoordinates.symm (root.symm x) =
    euclideanCoordinates.symm (root.symm w)-euclideanCoordinates.symm (root.symm z)
  rw [←displacementPullback_sub,←displacementPullback_sub,h]

theorem registered_development_translation (root : EPlane ≃ᵢ EPlane)
    (x z v : EPlane)
    (hx : sourcePoint root x ∈ quadraticPlane) (hxv : sourcePoint root (x+v) ∈ quadraticPlane)
    (hz : sourcePoint root z ∈ quadraticPlane) (hzv : sourcePoint root (z+v) ∈ quadraticPlane) :
    physicalVertexDevelopment root (x+v)-physicalVertexDevelopment root x =
      physicalVertexDevelopment root (z+v)-physicalVertexDevelopment root z :=
  registered_development_displacement root x (x+v) z (z+v) hx hxv hz hzv
    (by simp only [add_sub_cancel_left])

end
end SpectreGeometry
