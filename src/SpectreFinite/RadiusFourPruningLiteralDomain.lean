module

public import SpectreFinite.RotatedWindows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def literalDomain : List Position := [(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),(-3,4),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),(-2,4),(-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(-1,4),(0,-4),(0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4),(1,-4),(1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,-4),(2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(3,-4),(3,-3),(3,-2),(3,-1),(3,0),(3,1),(4,-4),(4,-3),(4,-2),(4,-1),(4,0)]

end SpectreFinite.HexSearch.RadiusFourPruning
