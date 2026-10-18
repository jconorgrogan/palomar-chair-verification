module

public import SpectreFinite.RadiusOneThetaStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def thetaStage1 : List (List (Position × State)) := [[((-1,0),(0,1)),((0,0),(2,0))],[((-1,0),(1,5)),((0,0),(2,0))],[((-1,0),(6,5)),((0,0),(2,0))]]

theorem thetaStage1_exact : Search.enumerate (choices (2,0)) Matches [(-1,0),(0,0)] = thetaStage1 := by
  rw [enumerate_consRoot, thetaStage0_exact]
  simp only [thetaStage0, List.flatMap_cons, List.flatMap_nil, theta_extend_1_0]
  rfl
#print axioms thetaStage1_exact
end SpectreFinite.HexSearch.RadiusOne
