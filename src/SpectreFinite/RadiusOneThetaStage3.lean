module

public import SpectreFinite.RadiusOneThetaStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def thetaStage3 : List (List (Position × State)) := [[((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(2,0))],[((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(0,1)),((0,0),(2,0))],[((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))],[((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))]]

theorem thetaStage3_exact : Search.enumerate (choices (2,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = thetaStage3 := by
  rw [enumerate_consRoot, thetaStage2_exact]
  simp only [thetaStage2, List.flatMap_cons, List.flatMap_nil, theta_extend_3_0, theta_extend_3_1, theta_extend_3_2, theta_extend_3_3, theta_extend_3_4, theta_extend_3_5, theta_extend_3_6, theta_extend_3_7, theta_extend_3_8, theta_extend_3_9, theta_extend_3_10, theta_extend_3_11]
  rfl
#print axioms thetaStage3_exact
end SpectreFinite.HexSearch.RadiusOne
