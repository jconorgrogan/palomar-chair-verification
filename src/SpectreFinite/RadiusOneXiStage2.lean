module

public import SpectreFinite.RadiusOneXiStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def xiStage2 : List (List (Position × State)) := [[((0,-1),(1,2)),((-1,0),(0,2)),((0,0),(4,0))],[((0,-1),(3,2)),((-1,0),(0,2)),((0,0),(4,0))],[((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(4,0))],[((0,-1),(6,2)),((-1,0),(0,2)),((0,0),(4,0))],[((0,-1),(7,2)),((-1,0),(1,0)),((0,0),(4,0))],[((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(4,0))],[((0,-1),(7,2)),((-1,0),(3,0)),((0,0),(4,0))],[((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(4,0))],[((0,-1),(7,2)),((-1,0),(5,0)),((0,0),(4,0))],[((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(4,0))],[((0,-1),(7,2)),((-1,0),(6,0)),((0,0),(4,0))],[((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(4,0))]]

theorem xiStage2_exact : Search.enumerate (choices (4,0)) Matches [(0,-1),(-1,0),(0,0)] = xiStage2 := by
  rw [enumerate_consRoot, xiStage1_exact]
  simp only [xiStage1, List.flatMap_cons, List.flatMap_nil, xi_extend_2_0, xi_extend_2_1, xi_extend_2_2, xi_extend_2_3, xi_extend_2_4]
  rfl
#print axioms xiStage2_exact
end SpectreFinite.HexSearch.RadiusOne
