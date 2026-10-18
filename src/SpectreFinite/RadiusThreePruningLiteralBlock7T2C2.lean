module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_2_0 : List State := [(0,5),(4,4),(0,0),(3,2),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(0,4),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(0,5),(2,0),(7,3),(5,2),(8,0),(3,1),(0,1),(6,2),(8,4)]
def patch7_2_2_0 : Patch := literalDomain.zip stateRow7_2_2_0
theorem patch_states7_2_2_0 : patch7_2_2_0.map Prod.snd = stateRow7_2_2_0 := by rfl
def stateRow7_2_2_1 : List State := [(0,5),(4,4),(0,0),(7,2),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(0,4),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(0,5),(2,0),(7,3),(5,2),(8,0),(3,1),(0,1),(6,2),(8,4)]
def patch7_2_2_1 : Patch := literalDomain.zip stateRow7_2_2_1
theorem patch_states7_2_2_1 : patch7_2_2_1.map Prod.snd = stateRow7_2_2_1 := by rfl
def stateRow7_2_2_2 : List State := [(6,3),(2,2),(3,3),(5,2),(0,2),(1,1),(0,1),(6,2),(8,4),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,5),(7,0),(8,3),(5,5),(1,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_2 : Patch := literalDomain.zip stateRow7_2_2_2
theorem patch_states7_2_2_2 : patch7_2_2_2.map Prod.snd = stateRow7_2_2_2 := by rfl
def stateRow7_2_2_3 : List State := [(0,5),(2,0),(7,3),(5,2),(6,0),(3,1),(0,1),(6,2),(8,4),(8,2),(5,0),(4,5),(1,0),(7,1),(7,5),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,5),(7,0),(8,3),(5,5),(1,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_3 : Patch := literalDomain.zip stateRow7_2_2_3
theorem patch_states7_2_2_3 : patch7_2_2_3.map Prod.snd = stateRow7_2_2_3 := by rfl
def stateRow7_2_2_4 : List State := [(0,5),(2,4),(1,3),(5,2),(6,0),(7,1),(6,5),(0,4),(5,4),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(4,2),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(3,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_4 : Patch := literalDomain.zip stateRow7_2_2_4
theorem patch_states7_2_2_4 : patch7_2_2_4.map Prod.snd = stateRow7_2_2_4 := by rfl
def stateRow7_2_2_5 : List State := [(0,5),(4,4),(0,0),(3,2),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_5 : Patch := literalDomain.zip stateRow7_2_2_5
theorem patch_states7_2_2_5 : patch7_2_2_5.map Prod.snd = stateRow7_2_2_5 := by rfl
def stateRow7_2_2_6 : List State := [(0,5),(4,4),(0,0),(7,2),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_6 : Patch := literalDomain.zip stateRow7_2_2_6
theorem patch_states7_2_2_6 : patch7_2_2_6.map Prod.snd = stateRow7_2_2_6 := by rfl
def stateRow7_2_2_7 : List State := [(0,5),(2,4),(1,3),(5,2),(6,0),(7,1),(6,5),(0,4),(5,4),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(4,2),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_7 : Patch := literalDomain.zip stateRow7_2_2_7
theorem patch_states7_2_2_7 : patch7_2_2_7.map Prod.snd = stateRow7_2_2_7 := by rfl
def stateRow7_2_2_8 : List State := [(0,5),(2,4),(1,3),(5,2),(6,0),(7,1),(6,5),(0,4),(5,4),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,4),(1,4),(0,5),(4,4)]
def patch7_2_2_8 : Patch := literalDomain.zip stateRow7_2_2_8
theorem patch_states7_2_2_8 : patch7_2_2_8.map Prod.snd = stateRow7_2_2_8 := by rfl
def stateRow7_2_2_10 : List State := [(1,3),(4,2),(5,3),(5,5),(6,5),(0,4),(1,4),(0,5),(4,4),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,2),(7,4),(1,3),(8,2)]
def patch7_2_2_10 : Patch := literalDomain.zip stateRow7_2_2_10
theorem patch_states7_2_2_10 : patch7_2_2_10.map Prod.snd = stateRow7_2_2_10 := by rfl
def stateRow7_2_2_11 : List State := [(1,3),(4,2),(5,3),(5,5),(6,5),(0,4),(1,4),(0,5),(4,4),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,2),(7,4),(6,3),(7,2)]
def patch7_2_2_11 : Patch := literalDomain.zip stateRow7_2_2_11
theorem patch_states7_2_2_11 : patch7_2_2_11.map Prod.snd = stateRow7_2_2_11 := by rfl
def final7_2_2 : List Patch := [patch7_2_2_0, patch7_2_2_1, patch7_2_2_2, patch7_2_2_3, patch7_2_2_4, patch7_2_2_5, patch7_2_2_6, patch7_2_2_7, patch7_2_2_8, patch7_2_2_10, patch7_2_2_11]
def stateRows7_2_2 : List (List State) := [stateRow7_2_2_0, stateRow7_2_2_1, stateRow7_2_2_2, stateRow7_2_2_3, stateRow7_2_2_4, stateRow7_2_2_5, stateRow7_2_2_6, stateRow7_2_2_7, stateRow7_2_2_8, stateRow7_2_2_10, stateRow7_2_2_11]
theorem stateRows_eq7_2_2 : stateRows7_2_2 = final7_2_2.map (List.map Prod.snd) := by
  simp only [stateRows7_2_2, final7_2_2, List.map_cons, List.map_nil, patch_states7_2_2_0, patch_states7_2_2_1, patch_states7_2_2_2, patch_states7_2_2_3, patch_states7_2_2_4, patch_states7_2_2_5, patch_states7_2_2_6, patch_states7_2_2_7, patch_states7_2_2_8, patch_states7_2_2_10, patch_states7_2_2_11]
theorem final_states7_2_2 : final7_2_2 = stateRows7_2_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
