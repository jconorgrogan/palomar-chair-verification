module

public import SpectreGeometry.ReverseLocalStarCanonicalData
public import SpectreGeometry.ReverseLocalStarStructuralSoundness
public import SpectreGeometry.ReverseLocalStarReal

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set ReverseLocalStars ReverseClusterTriangulation

theorem canonicalStar_origin_interior (k : Fin 124) :
    (0:RealPoint) ∈ interior (starBody (canonicalStars.getD k.val [])) :=
  structural_origin_interior_of_scaled_packets (starFamily k) _
    (canonical_vertices_binding k) (all_star_certificates k).origin_interior

end
end SpectreGeometry.ReverseLocalStarOccurrences
