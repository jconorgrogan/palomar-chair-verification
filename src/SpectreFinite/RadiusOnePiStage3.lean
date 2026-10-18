module

public import SpectreFinite.RadiusOnePiStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def piStage3 : List (List (Position × State)) := [[((1,-1),(5,4)),((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(5,0))],[((1,-1),(8,4)),((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(5,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(5,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(5,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(5,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(5,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(5,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(5,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(5,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(5,0))]]

theorem piStage3_exact : Search.enumerate (choices (5,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = piStage3 := by
  rw [enumerate_consRoot, piStage2_exact]
  simp only [piStage2, List.flatMap_cons, List.flatMap_nil, pi_extend_3_0, pi_extend_3_1, pi_extend_3_2, pi_extend_3_3, pi_extend_3_4, pi_extend_3_5, pi_extend_3_6, pi_extend_3_7, pi_extend_3_8, pi_extend_3_9, pi_extend_3_10, pi_extend_3_11]
  rfl
#print axioms piStage3_exact
end SpectreFinite.HexSearch.RadiusOne
