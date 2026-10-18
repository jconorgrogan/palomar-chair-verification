module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow3_4_0_0 : List State := [(5,4),(6,4),(1,2),(8,4),(4,3),(7,5),(0,3),(8,1),(1,5),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(4,4),(6,4),(1,2),(4,0),(7,3),(7,5),(0,3),(5,1),(0,1)]
def patch3_4_0_0 : Patch := literalDomain.zip stateRow3_4_0_0
theorem patch_states3_4_0_0 : patch3_4_0_0.map Prod.snd = stateRow3_4_0_0 := by rfl
def stateRow3_4_0_1 : List State := [(5,4),(6,4),(1,2),(7,4),(4,3),(7,5),(0,3),(8,1),(6,5),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(4,4),(6,4),(1,2),(4,0),(7,3),(7,5),(0,3),(5,1),(0,1)]
def patch3_4_0_1 : Patch := literalDomain.zip stateRow3_4_0_1
theorem patch_states3_4_0_1 : patch3_4_0_1.map Prod.snd = stateRow3_4_0_1 := by rfl
def final3_4_0 : List Patch := [patch3_4_0_0, patch3_4_0_1]
def stateRows3_4_0 : List (List State) := [stateRow3_4_0_0, stateRow3_4_0_1]
theorem stateRows_eq3_4_0 : stateRows3_4_0 = final3_4_0.map (List.map Prod.snd) := by
  simp only [stateRows3_4_0, final3_4_0, List.map_cons, List.map_nil, patch_states3_4_0_0, patch_states3_4_0_1]
theorem final_states3_4_0 : final3_4_0 = stateRows3_4_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
