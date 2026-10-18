module

public import SpectreFinite.RadiusOnePiStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def piStage2 : List (List (Position × State)) := [[((0,-1),(1,2)),((-1,0),(0,2)),((0,0),(5,0))],[((0,-1),(3,2)),((-1,0),(0,2)),((0,0),(5,0))],[((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(5,0))],[((0,-1),(6,2)),((-1,0),(0,2)),((0,0),(5,0))],[((0,-1),(7,2)),((-1,0),(1,0)),((0,0),(5,0))],[((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(5,0))],[((0,-1),(7,2)),((-1,0),(3,0)),((0,0),(5,0))],[((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(5,0))],[((0,-1),(7,2)),((-1,0),(5,0)),((0,0),(5,0))],[((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(5,0))],[((0,-1),(7,2)),((-1,0),(6,0)),((0,0),(5,0))],[((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(5,0))]]

theorem piStage2_exact : Search.enumerate (choices (5,0)) Matches [(0,-1),(-1,0),(0,0)] = piStage2 := by
  rw [enumerate_consRoot, piStage1_exact]
  simp only [piStage1, List.flatMap_cons, List.flatMap_nil, pi_extend_2_0, pi_extend_2_1, pi_extend_2_2, pi_extend_2_3, pi_extend_2_4]
  rfl
#print axioms piStage2_exact
end SpectreFinite.HexSearch.RadiusOne
