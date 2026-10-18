module

public import SpectreFinite.RadiusOneSigmaStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def sigmaStage3 : List (List (Position × State)) := [[((1,-1),(7,2)),((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))],[((1,-1),(8,2)),((0,-1),(2,5)),((-1,0),(1,4)),((0,0),(6,0))],[((1,-1),(4,4)),((0,-1),(3,5)),((-1,0),(1,4)),((0,0),(6,0))],[((1,-1),(7,2)),((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))],[((1,-1),(8,2)),((0,-1),(7,5)),((-1,0),(1,4)),((0,0),(6,0))]]

theorem sigmaStage3_exact : Search.enumerate (choices (6,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = sigmaStage3 := by
  rw [enumerate_consRoot, sigmaStage2_exact]
  simp only [sigmaStage2, List.flatMap_cons, List.flatMap_nil, sigma_extend_3_0, sigma_extend_3_1, sigma_extend_3_2]
  rfl
#print axioms sigmaStage3_exact
end SpectreFinite.HexSearch.RadiusOne
