module

public import SpectreFinite.RadiusFourPruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_0_4_0 : List State := [(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(2,3),(0,5),(4,4),(1,4),(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(6,5),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(5,4),(6,4),(1,2),(7,4),(6,3)]
def patch8_0_4_0 : Patch := literalDomain.zip stateRow8_0_4_0
theorem patch_states8_0_4_0 : patch8_0_4_0.map Prod.snd = stateRow8_0_4_0 := by rfl
def stateRow8_0_4_1 : List State := [(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,3),(0,5),(4,4),(1,4),(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(6,0),(3,1),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(5,1),(0,1),(6,2),(7,4),(6,3)]
def patch8_0_4_1 : Patch := literalDomain.zip stateRow8_0_4_1
theorem patch_states8_0_4_1 : patch8_0_4_1.map Prod.snd = stateRow8_0_4_1 := by rfl
def stateRow8_0_4_2 : List State := [(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,3),(0,5),(4,4),(1,4),(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(6,0),(3,1),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(5,4),(6,4),(1,2),(7,4),(6,3)]
def patch8_0_4_2 : Patch := literalDomain.zip stateRow8_0_4_2
theorem patch_states8_0_4_2 : patch8_0_4_2.map Prod.snd = stateRow8_0_4_2 := by rfl
def stateRow8_0_4_3 : List State := [(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,3),(0,5),(4,4),(1,4),(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(5,1),(0,1),(6,2),(7,4),(6,3)]
def patch8_0_4_3 : Patch := literalDomain.zip stateRow8_0_4_3
theorem patch_states8_0_4_3 : patch8_0_4_3.map Prod.snd = stateRow8_0_4_3 := by rfl
def final8_0_4 : List Patch := [patch8_0_4_0, patch8_0_4_1, patch8_0_4_2, patch8_0_4_3]
def stateRows8_0_4 : List (List State) := [stateRow8_0_4_0, stateRow8_0_4_1, stateRow8_0_4_2, stateRow8_0_4_3]
theorem stateRows_eq8_0_4 : stateRows8_0_4 = final8_0_4.map (List.map Prod.snd) := by
  simp only [stateRows8_0_4, final8_0_4, List.map_cons, List.map_nil, patch_states8_0_4_0, patch_states8_0_4_1, patch_states8_0_4_2, patch_states8_0_4_3]
theorem final_states8_0_4 : final8_0_4 = stateRows8_0_4.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFourPruning
