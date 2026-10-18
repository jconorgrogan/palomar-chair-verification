module

public import SpectreFinite.RadiusOneSigmaStage1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sigma_extend_2_0 : extendRoot (6,0) (0,-1) [((-1,0),(1,4)),((0,0),(6,0))] = [[((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))],[((0,-1),(3,5)),((-1,0),(1,4)),((0,0),(6,0))],[((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
