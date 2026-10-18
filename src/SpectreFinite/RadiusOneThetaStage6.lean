module

public import SpectreFinite.RadiusOneThetaStage6Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def thetaStage6 : List (List (Position × State)) := [[((-1,1),(6,1)),((0,1),(7,3)),((1,0),(0,1)),((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((-1,1),(6,1)),((0,1),(8,3)),((1,0),(0,1)),((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((-1,1),(6,1)),((0,1),(7,3)),((1,0),(0,1)),((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((-1,1),(6,1)),((0,1),(8,3)),((1,0),(0,1)),((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(1,5)),((0,0),(2,0))],[((-1,1),(0,4)),((0,1),(2,3)),((1,0),(0,1)),((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))],[((-1,1),(0,4)),((0,1),(4,3)),((1,0),(0,1)),((1,-1),(3,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))],[((-1,1),(0,4)),((0,1),(2,3)),((1,0),(0,1)),((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))],[((-1,1),(0,4)),((0,1),(4,3)),((1,0),(0,1)),((1,-1),(5,1)),((0,-1),(0,5)),((-1,0),(6,5)),((0,0),(2,0))]]

theorem thetaStage6_exact : Search.enumerate (choices (2,0)) Matches [(-1,1),(0,1),(1,0),(1,-1),(0,-1),(-1,0),(0,0)] = thetaStage6 := by
  rw [enumerate_consRoot, thetaStage5_exact]
  simp only [thetaStage5, List.flatMap_cons, List.flatMap_nil, theta_extend_6_0, theta_extend_6_1, theta_extend_6_2, theta_extend_6_3, theta_extend_6_4, theta_extend_6_5, theta_extend_6_6, theta_extend_6_7, theta_extend_6_8, theta_extend_6_9, theta_extend_6_10, theta_extend_6_11, theta_extend_6_12, theta_extend_6_13, theta_extend_6_14, theta_extend_6_15, theta_extend_6_16, theta_extend_6_17, theta_extend_6_18, theta_extend_6_19, theta_extend_6_20, theta_extend_6_21, theta_extend_6_22, theta_extend_6_23]
  rfl
#print axioms thetaStage6_exact
end SpectreFinite.HexSearch.RadiusOne
