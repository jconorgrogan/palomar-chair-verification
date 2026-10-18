module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_1_0_0 : List State := [(1,1),(4,1),(0,2),(1,1),(8,0),(7,3),(5,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(1,3),(4,2),(5,3),(8,5),(7,0),(8,3),(0,4),(3,4),(6,3),(7,2),(7,4),(2,3),(0,2),(1,1),(4,1)]
def patch8_1_0_0 : Patch := literalDomain.zip stateRow8_1_0_0
theorem patch_states8_1_0_0 : patch8_1_0_0.map Prod.snd = stateRow8_1_0_0 := by rfl
def stateRow8_1_0_1 : List State := [(1,1),(4,1),(0,2),(1,1),(8,0),(7,3),(5,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(0,4),(1,4),(0,5),(4,4),(1,4),(2,5),(6,0),(7,1),(7,5)]
def patch8_1_0_1 : Patch := literalDomain.zip stateRow8_1_0_1
theorem patch_states8_1_0_1 : patch8_1_0_1.map Prod.snd = stateRow8_1_0_1 := by rfl
def stateRow8_1_0_2 : List State := [(7,1),(7,5),(0,3),(5,1),(8,0),(7,3),(4,2),(5,3),(8,5),(5,4),(6,4),(1,2),(7,4),(1,3),(8,2),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(1,3),(4,2),(5,3),(8,5),(7,0),(4,3),(0,4),(3,4),(6,3),(7,2),(7,4),(2,3),(0,2),(1,1),(4,1)]
def patch8_1_0_2 : Patch := literalDomain.zip stateRow8_1_0_2
theorem patch_states8_1_0_2 : patch8_1_0_2.map Prod.snd = stateRow8_1_0_2 := by rfl
def stateRow8_1_0_3 : List State := [(7,1),(7,5),(0,3),(5,1),(8,0),(7,3),(4,2),(5,3),(8,5),(5,4),(6,4),(1,2),(7,4),(1,3),(8,2),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(1,3),(4,2),(5,3),(5,5),(7,0),(4,3),(0,4),(1,4),(0,5),(4,4),(1,4),(2,5),(6,0),(7,1),(7,5)]
def patch8_1_0_3 : Patch := literalDomain.zip stateRow8_1_0_3
theorem patch_states8_1_0_3 : patch8_1_0_3.map Prod.snd = stateRow8_1_0_3 := by rfl
def stateRow8_1_0_4 : List State := [(7,1),(7,5),(6,0),(3,1),(8,0),(7,3),(8,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(1,3),(4,2),(5,3),(8,5),(7,0),(8,3),(0,4),(3,4),(6,3),(7,2),(7,4),(2,3),(0,2),(1,1),(4,1)]
def patch8_1_0_4 : Patch := literalDomain.zip stateRow8_1_0_4
theorem patch_states8_1_0_4 : patch8_1_0_4.map Prod.snd = stateRow8_1_0_4 := by rfl
def stateRow8_1_0_5 : List State := [(7,1),(7,5),(6,0),(7,1),(8,0),(7,3),(8,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(1,3),(4,2),(5,3),(8,5),(7,0),(8,3),(0,4),(3,4),(6,3),(7,2),(7,4),(2,3),(0,2),(1,1),(4,1)]
def patch8_1_0_5 : Patch := literalDomain.zip stateRow8_1_0_5
theorem patch_states8_1_0_5 : patch8_1_0_5.map Prod.snd = stateRow8_1_0_5 := by rfl
def stateRow8_1_0_6 : List State := [(7,1),(7,5),(6,0),(3,1),(8,0),(7,3),(8,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(0,4),(1,4),(0,5),(4,4),(1,4),(2,5),(6,0),(7,1),(7,5)]
def patch8_1_0_6 : Patch := literalDomain.zip stateRow8_1_0_6
theorem patch_states8_1_0_6 : patch8_1_0_6.map Prod.snd = stateRow8_1_0_6 := by rfl
def stateRow8_1_0_7 : List State := [(7,1),(7,5),(6,0),(7,1),(8,0),(7,3),(8,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(0,4),(1,4),(0,5),(4,4),(1,4),(2,5),(6,0),(7,1),(7,5)]
def patch8_1_0_7 : Patch := literalDomain.zip stateRow8_1_0_7
theorem patch_states8_1_0_7 : patch8_1_0_7.map Prod.snd = stateRow8_1_0_7 := by rfl
def stateRow8_1_0_10 : List State := [(1,1),(4,1),(0,2),(1,1),(8,0),(7,3),(5,2),(5,0),(4,5),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(1,2),(7,4),(6,3),(7,2),(7,4),(4,1),(0,2),(1,1),(8,1)]
def patch8_1_0_10 : Patch := literalDomain.zip stateRow8_1_0_10
theorem patch_states8_1_0_10 : patch8_1_0_10.map Prod.snd = stateRow8_1_0_10 := by rfl
def stateRow8_1_0_11 : List State := [(1,1),(4,1),(0,2),(1,1),(8,0),(7,3),(5,2),(5,0),(4,5),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(6,2),(7,4),(6,3),(7,2),(7,4),(2,1),(0,2),(1,1),(4,1)]
def patch8_1_0_11 : Patch := literalDomain.zip stateRow8_1_0_11
theorem patch_states8_1_0_11 : patch8_1_0_11.map Prod.snd = stateRow8_1_0_11 := by rfl
def final8_1_0 : List Patch := [patch8_1_0_0, patch8_1_0_1, patch8_1_0_2, patch8_1_0_3, patch8_1_0_4, patch8_1_0_5, patch8_1_0_6, patch8_1_0_7, patch8_1_0_10, patch8_1_0_11]
def stateRows8_1_0 : List (List State) := [stateRow8_1_0_0, stateRow8_1_0_1, stateRow8_1_0_2, stateRow8_1_0_3, stateRow8_1_0_4, stateRow8_1_0_5, stateRow8_1_0_6, stateRow8_1_0_7, stateRow8_1_0_10, stateRow8_1_0_11]
theorem stateRows_eq8_1_0 : stateRows8_1_0 = final8_1_0.map (List.map Prod.snd) := by
  simp only [stateRows8_1_0, final8_1_0, List.map_cons, List.map_nil, patch_states8_1_0_0, patch_states8_1_0_1, patch_states8_1_0_2, patch_states8_1_0_3, patch_states8_1_0_4, patch_states8_1_0_5, patch_states8_1_0_6, patch_states8_1_0_7, patch_states8_1_0_10, patch_states8_1_0_11]
theorem final_states8_1_0 : final8_1_0 = stateRows8_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
