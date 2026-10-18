module

public import SpectreFinite.RadiusOnePsiStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def psiStage2 : List (List (Position × State)) := [[((0,-1),(1,2)),((-1,0),(0,2)),((0,0),(8,0))],[((0,-1),(3,2)),((-1,0),(0,2)),((0,0),(8,0))],[((0,-1),(5,2)),((-1,0),(0,2)),((0,0),(8,0))],[((0,-1),(6,2)),((-1,0),(0,2)),((0,0),(8,0))],[((0,-1),(7,2)),((-1,0),(1,0)),((0,0),(8,0))],[((0,-1),(8,2)),((-1,0),(1,0)),((0,0),(8,0))],[((0,-1),(7,2)),((-1,0),(3,0)),((0,0),(8,0))],[((0,-1),(8,2)),((-1,0),(3,0)),((0,0),(8,0))],[((0,-1),(7,2)),((-1,0),(5,0)),((0,0),(8,0))],[((0,-1),(8,2)),((-1,0),(5,0)),((0,0),(8,0))],[((0,-1),(7,2)),((-1,0),(6,0)),((0,0),(8,0))],[((0,-1),(8,2)),((-1,0),(6,0)),((0,0),(8,0))]]

theorem psiStage2_exact : Search.enumerate (choices (8,0)) Matches [(0,-1),(-1,0),(0,0)] = psiStage2 := by
  rw [enumerate_consRoot, psiStage1_exact]
  simp only [psiStage1, List.flatMap_cons, List.flatMap_nil, psi_extend_2_0, psi_extend_2_1, psi_extend_2_2, psi_extend_2_3, psi_extend_2_4]
  rfl
#print axioms psiStage2_exact
end SpectreFinite.HexSearch.RadiusOne
