module

public import SpectreGeometry.ReverseClusterTriangulationSource06Cover08

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHexTree6 : CoverTree := sourceHex6Node0
theorem sourceFamily6_covered : checkTree (sourceHexFacets6 ++ [unitFacet]) (familyFacets sourceFamily6) sourceHexTree6 = true := sourceHex6Node0_checked


end SpectreGeometry.ReverseClusterTriangulation
