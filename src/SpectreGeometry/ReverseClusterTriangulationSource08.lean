module

public import SpectreGeometry.ReverseClusterTriangulationSource08Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree8 : CoverTree := sourceHex8Node0
theorem sourceFamily8_covered : checkTree (sourceHexFacets8 ++ [unitFacet]) (familyFacets sourceFamily8) sourceHexTree8 = true := sourceHex8Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
