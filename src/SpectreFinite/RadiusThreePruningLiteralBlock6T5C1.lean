module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_5_1_1 : List State := [(1,5),(6,1),(5,1),(0,1),(4,5),(7,0),(8,3),(8,5),(1,0),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(1,3),(0,2),(1,1),(8,1),(6,5)]
def patch6_5_1_1 : Patch := literalDomain.zip stateRow6_5_1_1
theorem patch_states6_5_1_1 : patch6_5_1_1.map Prod.snd = stateRow6_5_1_1 := by rfl
def stateRow6_5_1_2 : List State := [(1,5),(6,1),(5,1),(0,1),(4,5),(7,0),(8,3),(8,5),(1,0),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3),(0,2),(1,1),(4,1),(0,2)]
def patch6_5_1_2 : Patch := literalDomain.zip stateRow6_5_1_2
theorem patch_states6_5_1_2 : patch6_5_1_2.map Prod.snd = stateRow6_5_1_2 := by rfl
def stateRow6_5_1_3 : List State := [(6,5),(0,4),(5,4),(1,4),(4,5),(7,0),(4,3),(7,5),(6,0),(0,0),(7,2),(7,4),(1,3),(8,2),(5,0),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(0,0),(7,0),(8,3),(5,5),(7,0),(4,3),(1,5),(1,4),(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0)]
def patch6_5_1_3 : Patch := literalDomain.zip stateRow6_5_1_3
theorem patch_states6_5_1_3 : patch6_5_1_3.map Prod.snd = stateRow6_5_1_3 := by rfl
def stateRow6_5_1_4 : List State := [(6,5),(0,4),(5,4),(1,4),(4,5),(7,0),(4,3),(7,5),(6,0),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(5,5),(7,0),(4,3),(3,5),(1,4),(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0)]
def patch6_5_1_4 : Patch := literalDomain.zip stateRow6_5_1_4
theorem patch_states6_5_1_4 : patch6_5_1_4.map Prod.snd = stateRow6_5_1_4 := by rfl
def stateRow6_5_1_5 : List State := [(6,5),(0,4),(5,4),(1,4),(4,5),(7,0),(4,3),(7,5),(6,0),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(1,3),(0,2),(1,1),(8,1),(6,5)]
def patch6_5_1_5 : Patch := literalDomain.zip stateRow6_5_1_5
theorem patch_states6_5_1_5 : patch6_5_1_5.map Prod.snd = stateRow6_5_1_5 := by rfl
def stateRow6_5_1_6 : List State := [(6,5),(0,4),(5,4),(1,4),(4,5),(7,0),(4,3),(7,5),(6,0),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3),(0,2),(1,1),(4,1),(0,2)]
def patch6_5_1_6 : Patch := literalDomain.zip stateRow6_5_1_6
theorem patch_states6_5_1_6 : patch6_5_1_6.map Prod.snd = stateRow6_5_1_6 := by rfl
def stateRow6_5_1_7 : List State := [(6,5),(0,4),(5,4),(6,4),(4,5),(7,0),(4,3),(7,5),(0,3),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(6,0),(7,1),(1,5),(6,1)]
def patch6_5_1_7 : Patch := literalDomain.zip stateRow6_5_1_7
theorem patch_states6_5_1_7 : patch6_5_1_7.map Prod.snd = stateRow6_5_1_7 := by rfl
def stateRow6_5_1_8 : List State := [(6,5),(0,4),(5,4),(6,4),(8,5),(7,0),(4,3),(7,5),(0,3),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(0,2),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(6,0),(7,1),(1,5),(6,1)]
def patch6_5_1_8 : Patch := literalDomain.zip stateRow6_5_1_8
theorem patch_states6_5_1_8 : patch6_5_1_8.map Prod.snd = stateRow6_5_1_8 := by rfl
def stateRow6_5_1_9 : List State := [(6,5),(0,4),(5,4),(6,4),(4,5),(7,0),(4,3),(7,5),(0,3),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(1,5),(6,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(0,3)]
def patch6_5_1_9 : Patch := literalDomain.zip stateRow6_5_1_9
theorem patch_states6_5_1_9 : patch6_5_1_9.map Prod.snd = stateRow6_5_1_9 := by rfl
def stateRow6_5_1_10 : List State := [(6,5),(0,4),(5,4),(6,4),(8,5),(7,0),(4,3),(7,5),(0,3),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(0,3)]
def patch6_5_1_10 : Patch := literalDomain.zip stateRow6_5_1_10
theorem patch_states6_5_1_10 : patch6_5_1_10.map Prod.snd = stateRow6_5_1_10 := by rfl
def final6_5_1 : List Patch := [patch6_5_1_1, patch6_5_1_2, patch6_5_1_3, patch6_5_1_4, patch6_5_1_5, patch6_5_1_6, patch6_5_1_7, patch6_5_1_8, patch6_5_1_9, patch6_5_1_10]
def stateRows6_5_1 : List (List State) := [stateRow6_5_1_1, stateRow6_5_1_2, stateRow6_5_1_3, stateRow6_5_1_4, stateRow6_5_1_5, stateRow6_5_1_6, stateRow6_5_1_7, stateRow6_5_1_8, stateRow6_5_1_9, stateRow6_5_1_10]
theorem stateRows_eq6_5_1 : stateRows6_5_1 = final6_5_1.map (List.map Prod.snd) := by
  simp only [stateRows6_5_1, final6_5_1, List.map_cons, List.map_nil, patch_states6_5_1_1, patch_states6_5_1_2, patch_states6_5_1_3, patch_states6_5_1_4, patch_states6_5_1_5, patch_states6_5_1_6, patch_states6_5_1_7, patch_states6_5_1_8, patch_states6_5_1_9, patch_states6_5_1_10]
theorem final_states6_5_1 : final6_5_1 = stateRows6_5_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
