module

public import SpectreFinite.RadiusOneXiStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def xiStage1 : List (List (Position × State)) := [[((-1,0),(0,2)),((0,0),(4,0))],[((-1,0),(1,0)),((0,0),(4,0))],[((-1,0),(3,0)),((0,0),(4,0))],[((-1,0),(5,0)),((0,0),(4,0))],[((-1,0),(6,0)),((0,0),(4,0))]]

theorem xiStage1_exact : Search.enumerate (choices (4,0)) Matches [(-1,0),(0,0)] = xiStage1 := by
  rw [enumerate_consRoot, xiStage0_exact]
  simp only [xiStage0, List.flatMap_cons, List.flatMap_nil, xi_extend_1_0]
  rfl
#print axioms xiStage1_exact
end SpectreFinite.HexSearch.RadiusOne
