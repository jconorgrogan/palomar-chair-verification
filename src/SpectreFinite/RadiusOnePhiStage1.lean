module

public import SpectreFinite.RadiusOnePhiStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def phiStage1 : List (List (Position × State)) := [[((-1,0),(0,1)),((0,0),(7,0))],[((-1,0),(1,5)),((0,0),(7,0))],[((-1,0),(6,5)),((0,0),(7,0))]]

theorem phiStage1_exact : Search.enumerate (choices (7,0)) Matches [(-1,0),(0,0)] = phiStage1 := by
  rw [enumerate_consRoot, phiStage0_exact]
  simp only [phiStage0, List.flatMap_cons, List.flatMap_nil, phi_extend_1_0]
  rfl
#print axioms phiStage1_exact
end SpectreFinite.HexSearch.RadiusOne
