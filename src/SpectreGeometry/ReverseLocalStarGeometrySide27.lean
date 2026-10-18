module

public import SpectreGeometry.ReverseLocalStarGeometryValues

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem side_geometry_216 : SideGeometryCertificate 216 := by
  unfold SideGeometryCertificate
  decide
end SpectreGeometry.ReverseLocalStarOccurrences
