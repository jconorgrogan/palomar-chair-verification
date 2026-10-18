module

public import SpectreFinite.RadiusOnePsiStage1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def psiStage1 : List (List (Position × State)) := [[((-1,0),(0,2)),((0,0),(8,0))],[((-1,0),(1,0)),((0,0),(8,0))],[((-1,0),(3,0)),((0,0),(8,0))],[((-1,0),(5,0)),((0,0),(8,0))],[((-1,0),(6,0)),((0,0),(8,0))]]

theorem psiStage1_exact : Search.enumerate (choices (8,0)) Matches [(-1,0),(0,0)] = psiStage1 := by
  rw [enumerate_consRoot, psiStage0_exact]
  simp only [psiStage0, List.flatMap_cons, List.flatMap_nil, psi_extend_1_0]
  rfl
#print axioms psiStage1_exact
end SpectreFinite.HexSearch.RadiusOne
