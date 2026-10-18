module

public import SpectreFinite.RadiusThreePruningGeometry

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def tree2_5 : KeyTree := (.node 0 .empty .empty)

end SpectreFinite.HexSearch.RadiusThreePruning
