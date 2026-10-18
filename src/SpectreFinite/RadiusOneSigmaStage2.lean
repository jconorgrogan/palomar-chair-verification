module

public import SpectreFinite.RadiusOneSigmaStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def sigmaStage2 : List (List (Position × State)) := [[((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))],[((0,-1),(3,5)),((-1,0),(1,4)),((0,0),(6,0))],[((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))]]

theorem sigmaStage2_exact : Search.enumerate (choices (6,0)) Matches [(0,-1),(-1,0),(0,0)] = sigmaStage2 := by
  rw [enumerate_consRoot, sigmaStage1_exact]
  simp only [sigmaStage1, List.flatMap_cons, List.flatMap_nil, sigma_extend_2_0]
  rfl
#print axioms sigmaStage2_exact
end SpectreFinite.HexSearch.RadiusOne
