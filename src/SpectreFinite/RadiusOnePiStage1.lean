module

public import SpectreFinite.RadiusOnePiStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def piStage1 : List (List (Position × State)) := [[((-1,0),(0,2)),((0,0),(5,0))],[((-1,0),(1,0)),((0,0),(5,0))],[((-1,0),(3,0)),((0,0),(5,0))],[((-1,0),(5,0)),((0,0),(5,0))],[((-1,0),(6,0)),((0,0),(5,0))]]

theorem piStage1_exact : Search.enumerate (choices (5,0)) Matches [(-1,0),(0,0)] = piStage1 := by
  rw [enumerate_consRoot, piStage0_exact]
  simp only [piStage0, List.flatMap_cons, List.flatMap_nil, pi_extend_1_0]
  rfl
#print axioms piStage1_exact
end SpectreFinite.HexSearch.RadiusOne
