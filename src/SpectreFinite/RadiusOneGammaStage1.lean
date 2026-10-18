module

public import SpectreFinite.RadiusOneGammaStage0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem gamma_extend_1_0 : extend (0,0) (-1,0) [((0,0),(0,0))] = [[((-1,0),(0,2)),((0,0),(0,0))],[((-1,0),(1,0)),((0,0),(0,0))],[((-1,0),(3,0)),((0,0),(0,0))],[((-1,0),(5,0)),((0,0),(0,0))],[((-1,0),(6,0)),((0,0),(0,0))]] := by decide

def gammaStage1 : List (List (Position × State)) := [[((-1,0),(0,2)),((0,0),(0,0))],[((-1,0),(1,0)),((0,0),(0,0))],[((-1,0),(3,0)),((0,0),(0,0))],[((-1,0),(5,0)),((0,0),(0,0))],[((-1,0),(6,0)),((0,0),(0,0))]]

theorem gammaStage1_exact : Search.enumerate (choices (0,0)) Matches [(-1,0),(0,0)] = gammaStage1 := by
  rw [enumerate_cons, gammaStage0_exact]
  simp only [gammaStage0, List.flatMap_cons, List.flatMap_nil, gamma_extend_1_0]
  rfl
#print axioms gammaStage1_exact
end SpectreFinite.HexSearch.RadiusOne
