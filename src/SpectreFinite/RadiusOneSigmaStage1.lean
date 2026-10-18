module

public import SpectreFinite.RadiusOneSigmaStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def sigmaStage1 : List (List (Position × State)) := [[((-1,0),(1,4)),((0,0),(6,0))]]

theorem sigmaStage1_exact : Search.enumerate (choices (6,0)) Matches [(-1,0),(0,0)] = sigmaStage1 := by
  rw [enumerate_consRoot, sigmaStage0_exact]
  simp only [sigmaStage0, List.flatMap_cons, List.flatMap_nil, sigma_extend_1_0]
  rfl
#print axioms sigmaStage1_exact
end SpectreFinite.HexSearch.RadiusOne
