module

public import SpectreFinite.RadiusOnePhiStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def phiStage2 : List (List (Position × State)) := [[((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(7,0))],[((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(7,0))],[((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(7,0))],[((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(7,0))],[((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(7,0))],[((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(7,0))],[((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(7,0))],[((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(7,0))],[((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(7,0))],[((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(7,0))],[((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(7,0))],[((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(7,0))]]

theorem phiStage2_exact : Search.enumerate (choices (7,0)) Matches [(0,-1),(-1,0),(0,0)] = phiStage2 := by
  rw [enumerate_consRoot, phiStage1_exact]
  simp only [phiStage1, List.flatMap_cons, List.flatMap_nil, phi_extend_2_0, phi_extend_2_1, phi_extend_2_2]
  rfl
#print axioms phiStage2_exact
end SpectreFinite.HexSearch.RadiusOne
