module

public import SpectreGeometry.ReverseClusterTriangulationSource04Cover07

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree4 : CoverTree := sourceHex4Node0
theorem sourceFamily4_covered : checkTree (sourceHexFacets4 ++ [unitFacet]) (familyFacets sourceFamily4) sourceHexTree4 = true := sourceHex4Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
