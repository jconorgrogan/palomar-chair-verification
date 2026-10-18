module

public import SpectreFinite.RadiusOneLambdaStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def lambdaStage1 : List (List (Position × State)) := [[((-1,0),(0,1)),((0,0),(3,0))],[((-1,0),(1,5)),((0,0),(3,0))],[((-1,0),(6,5)),((0,0),(3,0))]]

theorem lambdaStage1_exact : Search.enumerate (choices (3,0)) Matches [(-1,0),(0,0)] = lambdaStage1 := by
  rw [enumerate_consRoot, lambdaStage0_exact]
  simp only [lambdaStage0, List.flatMap_cons, List.flatMap_nil, lambda_extend_1_0]
  rfl
#print axioms lambdaStage1_exact
end SpectreFinite.HexSearch.RadiusOne
