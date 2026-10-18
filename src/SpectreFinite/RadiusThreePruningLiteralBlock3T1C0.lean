module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow3_1_0_0 : List State := [(0,4),(5,4),(0,0),(7,2),(7,0),(4,3),(1,5),(6,1),(4,1),(4,4),(1,4),(0,5),(2,0),(7,3),(5,2),(7,1),(7,5),(6,0),(3,1),(0,1),(6,2),(8,4),(7,3),(8,2),(5,0),(4,5),(1,0),(7,1),(1,2),(8,4),(0,0),(7,2),(4,0),(8,1),(1,5),(6,1),(5,1)]
def patch3_1_0_0 : Patch := literalDomain.zip stateRow3_1_0_0
theorem patch_states3_1_0_0 : patch3_1_0_0.map Prod.snd = stateRow3_1_0_0 := by rfl
def stateRow3_1_0_1 : List State := [(0,4),(5,4),(0,0),(7,2),(7,0),(4,3),(1,5),(6,1),(4,1),(4,4),(1,4),(0,5),(2,0),(7,3),(5,2),(7,1),(7,5),(6,0),(3,1),(0,1),(6,2),(8,4),(7,3),(8,2),(5,0),(4,5),(1,0),(7,1),(6,2),(8,4),(0,0),(7,2),(4,0),(7,1),(1,5),(6,1),(5,1)]
def patch3_1_0_1 : Patch := literalDomain.zip stateRow3_1_0_1
theorem patch_states3_1_0_1 : patch3_1_0_1.map Prod.snd = stateRow3_1_0_1 := by rfl
def final3_1_0 : List Patch := [patch3_1_0_0, patch3_1_0_1]
def stateRows3_1_0 : List (List State) := [stateRow3_1_0_0, stateRow3_1_0_1]
theorem stateRows_eq3_1_0 : stateRows3_1_0 = final3_1_0.map (List.map Prod.snd) := by
  simp only [stateRows3_1_0, final3_1_0, List.map_cons, List.map_nil, patch_states3_1_0_0, patch_states3_1_0_1]
theorem final_states3_1_0 : final3_1_0 = stateRows3_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
