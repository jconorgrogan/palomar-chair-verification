module

public import SpectreFinite.RadiusOneThetaStage2Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def thetaStage2 : List (List (Position × State)) := [[((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(2,0))],[((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(2,0))],[((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(2,0))],[((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(2,0))],[((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(2,0))],[((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(2,0))],[((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(2,0))],[((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))],[((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(2,0))],[((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(2,0))],[((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(2,0))]]

theorem thetaStage2_exact : Search.enumerate (choices (2,0)) Matches [(0,-1),(-1,0),(0,0)] = thetaStage2 := by
  rw [enumerate_consRoot, thetaStage1_exact]
  simp only [thetaStage1, List.flatMap_cons, List.flatMap_nil, theta_extend_2_0, theta_extend_2_1, theta_extend_2_2]
  rfl
#print axioms thetaStage2_exact
end SpectreFinite.HexSearch.RadiusOne
