module

public import SpectreFinite.RotatedWindows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def patch2_2_0 : Patch := [((-2,0),(5,4)),((-2,1),(6,4)),((-2,2),(1,2)),((-1,-1),(4,3)),((-1,0),(7,5)),((-1,1),(0,3)),((-1,2),(4,1)),((0,-2),(7,4)),((0,-1),(6,3)),((0,0),(2,2)),((0,1),(3,3)),((0,2),(5,2)),((1,-2),(0,2)),((1,-1),(1,1)),((1,0),(0,1)),((1,1),(6,2)),((2,-2),(5,0)),((2,-1),(4,5)),((2,0),(1,0))]
def final2_2 : List Patch := [patch2_2_0]

end SpectreFinite.HexSearch.RadiusTwoPruning
