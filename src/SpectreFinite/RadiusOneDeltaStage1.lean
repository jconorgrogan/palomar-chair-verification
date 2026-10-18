module

public import SpectreFinite.RadiusOneDeltaStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def deltaStage1 : List (List (Position × State)) := [[((-1,0),(0,1)),((0,0),(1,0))],[((-1,0),(1,5)),((0,0),(1,0))],[((-1,0),(6,5)),((0,0),(1,0))]]

theorem deltaStage1_exact : Search.enumerate (choices (1,0)) Matches [(-1,0),(0,0)] = deltaStage1 := by
  rw [enumerate_consRoot, deltaStage0_exact]
  simp only [deltaStage0, List.flatMap_cons, List.flatMap_nil, delta_extend_1_0]
  rfl
#print axioms deltaStage1_exact
end SpectreFinite.HexSearch.RadiusOne
