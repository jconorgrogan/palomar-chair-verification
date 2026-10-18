module

public import SpectreGeometry.ReverseClusterTriangulationSource01Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree1 : CoverTree := sourceHex1Node0
theorem sourceFamily1_covered : checkTree (sourceHexFacets1 ++ [unitFacet]) (familyFacets sourceFamily1) sourceHexTree1 = true := sourceHex1Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
