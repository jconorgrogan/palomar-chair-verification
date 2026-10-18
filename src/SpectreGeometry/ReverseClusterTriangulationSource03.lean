module

public import SpectreGeometry.ReverseClusterTriangulationSource03Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree3 : CoverTree := sourceHex3Node0
theorem sourceFamily3_covered : checkTree (sourceHexFacets3 ++ [unitFacet]) (familyFacets sourceFamily3) sourceHexTree3 = true := sourceHex3Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
