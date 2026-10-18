module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_2_3_0 : List State := [(5,5),(7,0),(8,3),(5,5),(0,5),(4,4),(1,4),(0,5),(4,4),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,5),(1,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2)]
def patch8_2_3_0 : Patch := literalDomain.zip stateRow8_2_3_0
theorem patch_states8_2_3_0 : patch8_2_3_0.map Prod.snd = stateRow8_2_3_0 := by rfl
def stateRow8_2_3_1 : List State := [(5,5),(7,0),(8,3),(5,5),(0,5),(4,4),(1,4),(0,5),(4,4),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(8,2),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,5),(1,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2)]
def patch8_2_3_1 : Patch := literalDomain.zip stateRow8_2_3_1
theorem patch_states8_2_3_1 : patch8_2_3_1.map Prod.snd = stateRow8_2_3_1 := by rfl
def final8_2_3 : List Patch := [patch8_2_3_0, patch8_2_3_1]
def stateRows8_2_3 : List (List State) := [stateRow8_2_3_0, stateRow8_2_3_1]
theorem stateRows_eq8_2_3 : stateRows8_2_3 = final8_2_3.map (List.map Prod.snd) := by
  simp only [stateRows8_2_3, final8_2_3, List.map_cons, List.map_nil, patch_states8_2_3_0, patch_states8_2_3_1]
theorem final_states8_2_3 : final8_2_3 = stateRows8_2_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
