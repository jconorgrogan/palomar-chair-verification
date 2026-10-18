module

public import SpectreFinite.RadiusOneDeltaStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def deltaStage2 : List (List (Position × State)) := [[((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(1,0))],[((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(1,0))],[((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(1,0))],[((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(1,0))],[((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(1,0))],[((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(1,0))],[((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(1,0))],[((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(1,0))],[((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(1,0))],[((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(1,0))],[((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(1,0))],[((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(1,0))]]

theorem deltaStage2_exact : Search.enumerate (choices (1,0)) Matches [(0,-1),(-1,0),(0,0)] = deltaStage2 := by
  rw [enumerate_consRoot, deltaStage1_exact]
  simp only [deltaStage1, List.flatMap_cons, List.flatMap_nil, delta_extend_2_0, delta_extend_2_1, delta_extend_2_2]
  rfl
#print axioms deltaStage2_exact
end SpectreFinite.HexSearch.RadiusOne
