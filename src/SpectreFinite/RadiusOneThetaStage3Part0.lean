module

public import SpectreFinite.RadiusOneThetaStage2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem theta_extend_3_0 : extendRoot (2,0) (1,-1) [((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(2,0))] = [[((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(2,0))],[((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(2,0))]] := by decide
theorem theta_extend_3_1 : extendRoot (2,0) (1,-1) [((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_2 : extendRoot (2,0) (1,-1) [((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_3 : extendRoot (2,0) (1,-1) [((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_4 : extendRoot (2,0) (1,-1) [((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))] = [[((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))]] := by decide
theorem theta_extend_3_5 : extendRoot (2,0) (1,-1) [((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_6 : extendRoot (2,0) (1,-1) [((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_7 : extendRoot (2,0) (1,-1) [((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_8 : extendRoot (2,0) (1,-1) [((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))] = [[((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))],[((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))]] := by decide
theorem theta_extend_3_9 : extendRoot (2,0) (1,-1) [((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_10 : extendRoot (2,0) (1,-1) [((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(2,0))] = [] := by decide
theorem theta_extend_3_11 : extendRoot (2,0) (1,-1) [((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(2,0))] = [] := by decide
end SpectreFinite.HexSearch.RadiusOne
