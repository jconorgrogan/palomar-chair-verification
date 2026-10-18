module

public import SpectreFinite.RadiusFourPruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_1_4_0 : List State := [(0,5),(2,4),(1,3),(5,2),(8,0),(6,0),(7,1),(6,5),(0,4),(5,4),(1,4),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(6,0),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(1,3),(6,1),(4,1),(0,2),(1,1),(8,1),(6,5),(7,3),(5,2),(8,0),(8,3),(5,5)]
def patch8_1_4_0 : Patch := literalDomain.zip stateRow8_1_4_0
theorem patch_states8_1_4_0 : patch8_1_4_0.map Prod.snd = stateRow8_1_4_0 := by rfl
def stateRow8_1_4_1 : List State := [(0,5),(4,4),(0,0),(3,2),(4,0),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(6,3),(6,1),(4,1),(0,2),(1,1),(4,1),(0,2),(7,3),(5,2),(8,0),(7,3),(5,2)]
def patch8_1_4_1 : Patch := literalDomain.zip stateRow8_1_4_1
theorem patch_states8_1_4_1 : patch8_1_4_1.map Prod.snd = stateRow8_1_4_1 := by rfl
def stateRow8_1_4_2 : List State := [(0,5),(4,4),(0,0),(3,2),(4,0),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(1,3),(6,1),(4,1),(0,2),(1,1),(8,1),(6,5),(7,3),(5,2),(8,0),(8,3),(5,5)]
def patch8_1_4_2 : Patch := literalDomain.zip stateRow8_1_4_2
theorem patch_states8_1_4_2 : patch8_1_4_2.map Prod.snd = stateRow8_1_4_2 := by rfl
def stateRow8_1_4_3 : List State := [(0,5),(4,4),(0,0),(7,2),(4,0),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(6,3),(6,1),(4,1),(0,2),(1,1),(4,1),(0,2),(7,3),(5,2),(8,0),(7,3),(5,2)]
def patch8_1_4_3 : Patch := literalDomain.zip stateRow8_1_4_3
theorem patch_states8_1_4_3 : patch8_1_4_3.map Prod.snd = stateRow8_1_4_3 := by rfl
def final8_1_4 : List Patch := [patch8_1_4_0, patch8_1_4_1, patch8_1_4_2, patch8_1_4_3]
def stateRows8_1_4 : List (List State) := [stateRow8_1_4_0, stateRow8_1_4_1, stateRow8_1_4_2, stateRow8_1_4_3]
theorem stateRows_eq8_1_4 : stateRows8_1_4 = final8_1_4.map (List.map Prod.snd) := by
  simp only [stateRows8_1_4, final8_1_4, List.map_cons, List.map_nil, patch_states8_1_4_0, patch_states8_1_4_1, patch_states8_1_4_2, patch_states8_1_4_3]
theorem final_states8_1_4 : final8_1_4 = stateRows8_1_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFourPruning
