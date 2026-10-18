module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_0_0_0 : List State := [(7,5),(0,3),(4,1),(0,2),(6,3),(2,2),(3,3),(5,2),(8,0),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(1,5),(6,1),(5,1),(0,1),(6,2),(7,0),(8,3),(8,5),(1,0)]
def patch1_0_0_0 : Patch := literalDomain.zip stateRow1_0_0_0
theorem patch_states1_0_0_0 : patch1_0_0_0.map Prod.snd = stateRow1_0_0_0 := by rfl
def stateRow1_0_0_1 : List State := [(7,5),(0,3),(4,1),(0,2),(6,3),(2,2),(3,3),(5,2),(8,0),(0,2),(1,1),(0,1),(6,2),(8,4),(6,4),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(0,3),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(1,5),(6,1),(5,1),(0,1),(6,2),(7,0),(8,3),(5,5),(1,0)]
def patch1_0_0_1 : Patch := literalDomain.zip stateRow1_0_0_1
theorem patch_states1_0_0_1 : patch1_0_0_1.map Prod.snd = stateRow1_0_0_1 := by rfl
def stateRow1_0_0_2 : List State := [(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2),(5,0),(0,3),(5,1),(0,1),(6,2),(8,4),(0,0),(4,2),(5,3),(8,5),(1,0),(7,1),(1,5),(6,1),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(6,5),(0,4),(5,4),(0,0),(7,2),(7,0),(4,3),(1,5),(6,1)]
def patch1_0_0_2 : Patch := literalDomain.zip stateRow1_0_0_2
theorem patch_states1_0_0_2 : patch1_0_0_2.map Prod.snd = stateRow1_0_0_2 := by rfl
def stateRow1_0_0_3 : List State := [(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2),(8,0),(0,3),(5,1),(0,1),(6,2),(8,4),(1,4),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(6,0),(7,4),(1,3),(8,2),(8,0),(7,3),(8,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(7,5),(0,3)]
def patch1_0_0_3 : Patch := literalDomain.zip stateRow1_0_0_3
theorem patch_states1_0_0_3 : patch1_0_0_3.map Prod.snd = stateRow1_0_0_3 := by rfl
def stateRow1_0_0_4 : List State := [(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2),(8,0),(0,3),(5,1),(0,1),(6,2),(8,4),(6,4),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(3,5),(0,3)]
def patch1_0_0_4 : Patch := literalDomain.zip stateRow1_0_0_4
theorem patch_states1_0_0_4 : patch1_0_0_4.map Prod.snd = stateRow1_0_0_4 := by rfl
def stateRow1_0_0_5 : List State := [(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2),(8,0),(0,3),(5,1),(0,1),(6,2),(8,4),(6,4),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(7,5),(0,3)]
def patch1_0_0_5 : Patch := literalDomain.zip stateRow1_0_0_5
theorem patch_states1_0_0_5 : patch1_0_0_5.map Prod.snd = stateRow1_0_0_5 := by rfl
def stateRow1_0_0_6 : List State := [(0,2),(1,1),(4,1),(0,2),(1,2),(4,0),(7,3),(5,2),(8,0),(0,3),(5,1),(0,1),(6,2),(8,4),(6,4),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(0,2),(1,1),(5,1),(0,1),(6,2),(8,0),(8,3),(5,5),(1,0)]
def patch1_0_0_6 : Patch := literalDomain.zip stateRow1_0_0_6
theorem patch_states1_0_0_6 : patch1_0_0_6.map Prod.snd = stateRow1_0_0_6 := by rfl
def stateRow1_0_0_7 : List State := [(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2),(5,0),(6,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,0),(8,3),(8,5),(1,0),(7,1),(1,5),(6,1),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(6,5),(0,4),(5,4),(0,0),(7,2),(7,0),(4,3),(1,5),(6,1)]
def patch1_0_0_7 : Patch := literalDomain.zip stateRow1_0_0_7
theorem patch_states1_0_0_7 : patch1_0_0_7.map Prod.snd = stateRow1_0_0_7 := by rfl
def stateRow1_0_0_8 : List State := [(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2),(8,0),(6,1),(5,1),(0,1),(6,2),(8,4),(1,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(6,0),(7,4),(1,3),(8,2),(8,0),(7,3),(8,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(7,5),(0,3)]
def patch1_0_0_8 : Patch := literalDomain.zip stateRow1_0_0_8
theorem patch_states1_0_0_8 : patch1_0_0_8.map Prod.snd = stateRow1_0_0_8 := by rfl
def stateRow1_0_0_9 : List State := [(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2),(8,0),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(3,5),(0,3)]
def patch1_0_0_9 : Patch := literalDomain.zip stateRow1_0_0_9
theorem patch_states1_0_0_9 : patch1_0_0_9.map Prod.snd = stateRow1_0_0_9 := by rfl
def stateRow1_0_0_10 : List State := [(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2),(8,0),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(7,5),(0,3)]
def patch1_0_0_10 : Patch := literalDomain.zip stateRow1_0_0_10
theorem patch_states1_0_0_10 : patch1_0_0_10.map Prod.snd = stateRow1_0_0_10 := by rfl
def stateRow1_0_0_11 : List State := [(0,2),(1,1),(4,1),(0,2),(3,2),(4,0),(7,3),(5,2),(8,0),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(0,2),(1,1),(5,1),(0,1),(6,2),(8,0),(8,3),(5,5),(1,0)]
def patch1_0_0_11 : Patch := literalDomain.zip stateRow1_0_0_11
theorem patch_states1_0_0_11 : patch1_0_0_11.map Prod.snd = stateRow1_0_0_11 := by rfl
def final1_0_0 : List Patch := [patch1_0_0_0, patch1_0_0_1, patch1_0_0_2, patch1_0_0_3, patch1_0_0_4, patch1_0_0_5, patch1_0_0_6, patch1_0_0_7, patch1_0_0_8, patch1_0_0_9, patch1_0_0_10, patch1_0_0_11]
def stateRows1_0_0 : List (List State) := [stateRow1_0_0_0, stateRow1_0_0_1, stateRow1_0_0_2, stateRow1_0_0_3, stateRow1_0_0_4, stateRow1_0_0_5, stateRow1_0_0_6, stateRow1_0_0_7, stateRow1_0_0_8, stateRow1_0_0_9, stateRow1_0_0_10, stateRow1_0_0_11]
theorem stateRows_eq1_0_0 : stateRows1_0_0 = final1_0_0.map (List.map Prod.snd) := by
  simp only [stateRows1_0_0, final1_0_0, List.map_cons, List.map_nil, patch_states1_0_0_0, patch_states1_0_0_1, patch_states1_0_0_2, patch_states1_0_0_3, patch_states1_0_0_4, patch_states1_0_0_5, patch_states1_0_0_6, patch_states1_0_0_7, patch_states1_0_0_8, patch_states1_0_0_9, patch_states1_0_0_10, patch_states1_0_0_11]
theorem final_states1_0_0 : final1_0_0 = stateRows1_0_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
