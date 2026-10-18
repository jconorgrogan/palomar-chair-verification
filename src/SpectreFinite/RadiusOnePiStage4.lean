module

public import SpectreFinite.RadiusOnePiStage4Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def piStage4 : List (List (Position × State)) := [[((1,0),(0,0)),((1,-1),(5,4)),((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(8,4)),((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(5,0))],[((1,0),(0,0)),((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(5,0))]]

theorem piStage4_exact : Search.enumerate (choices (5,0)) Matches [(1,0),(1,-1),(0,-1),(-1,0),(0,0)] = piStage4 := by
  rw [enumerate_consRoot, piStage3_exact]
  simp only [piStage3, List.flatMap_cons, List.flatMap_nil, pi_extend_4_0, pi_extend_4_1, pi_extend_4_2, pi_extend_4_3, pi_extend_4_4, pi_extend_4_5, pi_extend_4_6, pi_extend_4_7, pi_extend_4_8, pi_extend_4_9]
  rfl
#print axioms piStage4_exact
end SpectreFinite.HexSearch.RadiusOne
