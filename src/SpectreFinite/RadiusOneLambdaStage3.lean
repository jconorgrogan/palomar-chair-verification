module

public import SpectreFinite.RadiusOneLambdaStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def lambdaStage3 : List (List (Position × State)) := [[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(3,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(3,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(3,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(3,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(3,0))],[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(3,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(3,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(3,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(3,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(3,0))],[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(3,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(3,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(3,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(3,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(3,0))]]

theorem lambdaStage3_exact : Search.enumerate (choices (3,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = lambdaStage3 := by
  rw [enumerate_consRoot, lambdaStage2_exact]
  simp only [lambdaStage2, List.flatMap_cons, List.flatMap_nil, lambda_extend_3_0, lambda_extend_3_1, lambda_extend_3_2, lambda_extend_3_3, lambda_extend_3_4, lambda_extend_3_5, lambda_extend_3_6, lambda_extend_3_7, lambda_extend_3_8, lambda_extend_3_9, lambda_extend_3_10, lambda_extend_3_11]
  rfl
#print axioms lambdaStage3_exact
end SpectreFinite.HexSearch.RadiusOne
