module

public import SpectreFinite.RadiusOnePsiStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def psiStage3 : List (List (Position × State)) := [[((1,-1),(5,4)),((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(8,0))],[((1,-1),(8,4)),((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(8,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(8,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(8,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(8,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(8,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(8,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(8,0))],[((1,-1),(5,4)),((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(8,0))],[((1,-1),(8,4)),((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(8,0))]]

theorem psiStage3_exact : Search.enumerate (choices (8,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = psiStage3 := by
  rw [enumerate_consRoot, psiStage2_exact]
  simp only [psiStage2, List.flatMap_cons, List.flatMap_nil, psi_extend_3_0, psi_extend_3_1, psi_extend_3_2, psi_extend_3_3, psi_extend_3_4, psi_extend_3_5, psi_extend_3_6, psi_extend_3_7, psi_extend_3_8, psi_extend_3_9, psi_extend_3_10, psi_extend_3_11]
  rfl
#print axioms psiStage3_exact
end SpectreFinite.HexSearch.RadiusOne
