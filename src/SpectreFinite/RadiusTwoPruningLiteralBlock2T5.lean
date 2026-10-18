module

public import SpectreFinite.RotatedWindows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def patch2_5_0 : Patch := [((-2,0),(1,3)),((-2,1),(4,2)),((-2,2),(5,3)),((-1,-1),(6,5)),((-1,0),(0,4)),((-1,1),(1,4)),((-1,2),(0,5)),((0,-2),(5,5)),((0,-1),(3,0)),((0,0),(2,5)),((0,1),(6,0)),((0,2),(7,1)),((1,-2),(4,4)),((1,-1),(0,0)),((1,0),(7,2)),((1,1),(4,0)),((2,-2),(1,5)),((2,-1),(6,1)),((2,0),(5,1))]
def final2_5 : List Patch := [patch2_5_0]

end SpectreFinite.HexSearch.RadiusTwoPruning
