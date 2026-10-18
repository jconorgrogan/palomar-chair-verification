module

public import SpectreFinite.RadiusOneSigmaStage2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sigma_extend_3_0 : extendRoot (6,0) (1,-1) [((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))] = [[((1,-1),(7,2)),((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))],[((1,-1),(8,2)),((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))]] := by decide
theorem sigma_extend_3_1 : extendRoot (6,0) (1,-1) [((0,-1),(3,5)),((-1,0),(1,4)),((0,0),(6,0))] = [[((1,-1),(4,4)),((0,-1),(3,5)),((-1,0),(1,4)),((0,0),(6,0))]] := by decide
theorem sigma_extend_3_2 : extendRoot (6,0) (1,-1) [((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))] = [[((1,-1),(7,2)),((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))],[((1,-1),(8,2)),((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
