module

public import SpectreFinite.RotatedWindows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def literalDomain : List Position := [(-3,0),(-3,1),(-3,2),(-3,3),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(3,-3),(3,-2),(3,-1),(3,0)]

end SpectreFinite.HexSearch.RadiusThreePruning
