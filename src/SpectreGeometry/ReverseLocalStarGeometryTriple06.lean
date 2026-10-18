module

public import SpectreGeometry.ReverseLocalStarGeometryValues

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem triple_geometry_48 : TripleGeometryCertificate 48 := by
  unfold TripleGeometryCertificate
  decide
end SpectreGeometry.ReverseLocalStarOccurrences
