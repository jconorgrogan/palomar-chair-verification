module

public import SpectreFinite.RadiusOnePhiStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def phiStage3 : List (List (Position × State)) := [[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(7,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(7,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(7,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(7,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(7,0))],[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(7,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(7,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(7,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(7,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(7,0))],[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(7,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(7,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(7,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(7,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(7,0))]]

theorem phiStage3_exact : Search.enumerate (choices (7,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = phiStage3 := by
  rw [enumerate_consRoot, phiStage2_exact]
  simp only [phiStage2, List.flatMap_cons, List.flatMap_nil, phi_extend_3_0, phi_extend_3_1, phi_extend_3_2, phi_extend_3_3, phi_extend_3_4, phi_extend_3_5, phi_extend_3_6, phi_extend_3_7, phi_extend_3_8, phi_extend_3_9, phi_extend_3_10, phi_extend_3_11]
  rfl
#print axioms phiStage3_exact
end SpectreFinite.HexSearch.RadiusOne
