module

public import SpectreFinite.RadiusOneLambdaStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def lambdaStage2 : List (List (Position × State)) := [[((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(3,0))],[((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(3,0))],[((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(3,0))],[((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(3,0))],[((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(3,0))],[((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(3,0))],[((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(3,0))],[((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(3,0))],[((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(3,0))],[((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(3,0))],[((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(3,0))],[((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(3,0))]]

theorem lambdaStage2_exact : Search.enumerate (choices (3,0)) Matches [(0,-1),(-1,0),(0,0)] = lambdaStage2 := by
  rw [enumerate_consRoot, lambdaStage1_exact]
  simp only [lambdaStage1, List.flatMap_cons, List.flatMap_nil, lambda_extend_2_0, lambda_extend_2_1, lambda_extend_2_2]
  rfl
#print axioms lambdaStage2_exact
end SpectreFinite.HexSearch.RadiusOne
