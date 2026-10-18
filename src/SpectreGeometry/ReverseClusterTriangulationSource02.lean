module

public import SpectreGeometry.ReverseClusterTriangulationSource02Cover07

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree2 : CoverTree := sourceHex2Node0
theorem sourceFamily2_covered : checkTree (sourceHexFacets2 ++ [unitFacet]) (familyFacets sourceFamily2) sourceHexTree2 = true := sourceHex2Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
