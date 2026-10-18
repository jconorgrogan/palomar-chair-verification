module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_5_1_0 : List State := [(4,5),(1,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,1),(0,2),(1,1),(5,1),(0,1),(5,2),(8,0),(8,3),(5,5)]
def patch8_5_1_0 : Patch := literalDomain.zip stateRow8_5_1_0
theorem patch_states8_5_1_0 : patch8_5_1_0.map Prod.snd = stateRow8_5_1_0 := by rfl
def stateRow8_5_1_1 : List State := [(4,5),(1,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(8,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,1),(0,2),(1,1),(5,1),(0,1),(5,2),(8,0),(8,3),(5,5)]
def patch8_5_1_1 : Patch := literalDomain.zip stateRow8_5_1_1
theorem patch_states8_5_1_1 : patch8_5_1_1.map Prod.snd = stateRow8_5_1_1 := by rfl
def stateRow8_5_1_2 : List State := [(4,5),(1,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(8,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(8,1),(6,5),(0,4),(5,4),(6,4),(5,5),(7,0),(4,3),(3,5)]
def patch8_5_1_2 : Patch := literalDomain.zip stateRow8_5_1_2
theorem patch_states8_5_1_2 : patch8_5_1_2.map Prod.snd = stateRow8_5_1_2 := by rfl
def stateRow8_5_1_3 : List State := [(2,5),(6,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,1),(0,2),(1,1),(5,1),(0,1),(5,2),(8,0),(8,3),(5,5)]
def patch8_5_1_3 : Patch := literalDomain.zip stateRow8_5_1_3
theorem patch_states8_5_1_3 : patch8_5_1_3.map Prod.snd = stateRow8_5_1_3 := by rfl
def stateRow8_5_1_4 : List State := [(2,5),(6,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(8,1),(6,5),(0,4),(5,4),(6,4),(5,5),(7,0),(4,3),(3,5)]
def patch8_5_1_4 : Patch := literalDomain.zip stateRow8_5_1_4
theorem patch_states8_5_1_4 : patch8_5_1_4.map Prod.snd = stateRow8_5_1_4 := by rfl
def stateRow8_5_1_5 : List State := [(2,5),(6,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(8,1),(6,5),(0,4),(5,4),(6,4),(8,5),(7,0),(4,3),(7,5)]
def patch8_5_1_5 : Patch := literalDomain.zip stateRow8_5_1_5
theorem patch_states8_5_1_5 : patch8_5_1_5.map Prod.snd = stateRow8_5_1_5 := by rfl
def stateRow8_5_1_6 : List State := [(7,3),(5,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(1,2),(7,4),(6,3),(7,2),(7,4),(1,3),(4,1),(0,2),(1,1),(8,1),(6,5),(5,2),(8,0),(8,3),(5,5)]
def patch8_5_1_6 : Patch := literalDomain.zip stateRow8_5_1_6
theorem patch_states8_5_1_6 : patch8_5_1_6.map Prod.snd = stateRow8_5_1_6 := by rfl
def stateRow8_5_1_7 : List State := [(7,3),(8,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(1,2),(7,4),(6,3),(7,2),(7,4),(1,3),(4,1),(0,2),(1,1),(8,1),(6,5),(5,2),(8,0),(8,3),(5,5)]
def patch8_5_1_7 : Patch := literalDomain.zip stateRow8_5_1_7
theorem patch_states8_5_1_7 : patch8_5_1_7.map Prod.snd = stateRow8_5_1_7 := by rfl
def stateRow8_5_1_8 : List State := [(7,3),(5,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(1,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(0,4),(3,4),(6,3),(7,2),(7,4),(6,3),(2,3),(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2)]
def patch8_5_1_8 : Patch := literalDomain.zip stateRow8_5_1_8
theorem patch_states8_5_1_8 : patch8_5_1_8.map Prod.snd = stateRow8_5_1_8 := by rfl
def stateRow8_5_1_9 : List State := [(7,3),(5,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(6,2),(7,4),(6,3),(7,2),(7,4),(6,3),(2,1),(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2)]
def patch8_5_1_9 : Patch := literalDomain.zip stateRow8_5_1_9
theorem patch_states8_5_1_9 : patch8_5_1_9.map Prod.snd = stateRow8_5_1_9 := by rfl
def stateRow8_5_1_10 : List State := [(7,3),(8,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(1,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(0,4),(3,4),(6,3),(7,2),(7,4),(6,3),(2,3),(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2)]
def patch8_5_1_10 : Patch := literalDomain.zip stateRow8_5_1_10
theorem patch_states8_5_1_10 : patch8_5_1_10.map Prod.snd = stateRow8_5_1_10 := by rfl
def stateRow8_5_1_11 : List State := [(7,3),(8,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(6,2),(7,4),(6,3),(7,2),(7,4),(6,3),(2,1),(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2)]
def patch8_5_1_11 : Patch := literalDomain.zip stateRow8_5_1_11
theorem patch_states8_5_1_11 : patch8_5_1_11.map Prod.snd = stateRow8_5_1_11 := by rfl
def final8_5_1 : List Patch := [patch8_5_1_0, patch8_5_1_1, patch8_5_1_2, patch8_5_1_3, patch8_5_1_4, patch8_5_1_5, patch8_5_1_6, patch8_5_1_7, patch8_5_1_8, patch8_5_1_9, patch8_5_1_10, patch8_5_1_11]
def stateRows8_5_1 : List (List State) := [stateRow8_5_1_0, stateRow8_5_1_1, stateRow8_5_1_2, stateRow8_5_1_3, stateRow8_5_1_4, stateRow8_5_1_5, stateRow8_5_1_6, stateRow8_5_1_7, stateRow8_5_1_8, stateRow8_5_1_9, stateRow8_5_1_10, stateRow8_5_1_11]
theorem stateRows_eq8_5_1 : stateRows8_5_1 = final8_5_1.map (List.map Prod.snd) := by
  simp only [stateRows8_5_1, final8_5_1, List.map_cons, List.map_nil, patch_states8_5_1_0, patch_states8_5_1_1, patch_states8_5_1_2, patch_states8_5_1_3, patch_states8_5_1_4, patch_states8_5_1_5, patch_states8_5_1_6, patch_states8_5_1_7, patch_states8_5_1_8, patch_states8_5_1_9, patch_states8_5_1_10, patch_states8_5_1_11]
theorem final_states8_5_1 : final8_5_1 = stateRows8_5_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
