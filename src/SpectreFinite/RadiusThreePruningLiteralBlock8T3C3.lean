module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_3_3_0 : List State := [(5,0),(4,5),(7,0),(4,3),(8,4),(0,0),(7,2),(7,4),(1,3),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(6,1),(4,1),(0,2),(1,1),(8,1),(7,3),(5,2),(8,0),(8,3)]
def patch8_3_3_0 : Patch := literalDomain.zip stateRow8_3_3_0
theorem patch_states8_3_3_0 : patch8_3_3_0.map Prod.snd = stateRow8_3_3_0 := by rfl
def stateRow8_3_3_1 : List State := [(5,0),(4,5),(7,0),(8,3),(8,4),(0,0),(7,2),(7,4),(1,3),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(6,1),(4,1),(0,2),(1,1),(8,1),(7,3),(5,2),(8,0),(8,3)]
def patch8_3_3_1 : Patch := literalDomain.zip stateRow8_3_3_1
theorem patch_states8_3_3_1 : patch8_3_3_1.map Prod.snd = stateRow8_3_3_1 := by rfl
def final8_3_3 : List Patch := [patch8_3_3_0, patch8_3_3_1]
def stateRows8_3_3 : List (List State) := [stateRow8_3_3_0, stateRow8_3_3_1]
theorem stateRows_eq8_3_3 : stateRows8_3_3 = final8_3_3.map (List.map Prod.snd) := by
  simp only [stateRows8_3_3, final8_3_3, List.map_cons, List.map_nil, patch_states8_3_3_0, patch_states8_3_3_1]
theorem final_states8_3_3 : final8_3_3 = stateRows8_3_3.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
