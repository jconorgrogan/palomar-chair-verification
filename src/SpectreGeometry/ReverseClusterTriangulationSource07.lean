module

public import SpectreGeometry.ReverseClusterTriangulationSource07Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree7 : CoverTree := sourceHex7Node0
theorem sourceFamily7_covered : checkTree (sourceHexFacets7 ++ [unitFacet]) (familyFacets sourceFamily7) sourceHexTree7 = true := sourceHex7Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
