module

public import SpectreGeometry.ReverseClusterTriangulationSource05Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree5 : CoverTree := sourceHex5Node0
theorem sourceFamily5_covered : checkTree (sourceHexFacets5 ++ [unitFacet]) (familyFacets sourceFamily5) sourceHexTree5 = true := sourceHex5Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
