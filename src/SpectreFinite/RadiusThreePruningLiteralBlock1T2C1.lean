module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_2_1_0 : List State := [(6,2),(8,4),(6,4),(1,2),(1,0),(7,1),(7,5),(0,3),(8,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(6,3),(2,2),(3,3),(5,2),(8,0),(1,1),(0,1),(6,2),(8,4)]
def patch1_2_1_0 : Patch := literalDomain.zip stateRow1_2_1_0
theorem patch_states1_2_1_0 : patch1_2_1_0.map Prod.snd = stateRow1_2_1_0 := by rfl
def stateRow1_2_1_1 : List State := [(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(0,3),(5,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(6,3),(2,2),(3,3),(5,2),(8,0),(1,1),(0,1),(6,2),(8,4)]
def patch1_2_1_1 : Patch := literalDomain.zip stateRow1_2_1_1
theorem patch_states1_2_1_1 : patch1_2_1_1.map Prod.snd = stateRow1_2_1_1 := by rfl
def stateRow1_2_1_2 : List State := [(1,3),(4,2),(5,3),(8,5),(6,5),(0,4),(3,4),(6,3),(7,2),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(7,3),(4,2),(5,3),(8,5),(1,0),(1,2),(7,4),(1,3),(8,2)]
def patch1_2_1_2 : Patch := literalDomain.zip stateRow1_2_1_2
theorem patch_states1_2_1_2 : patch1_2_1_2.map Prod.snd = stateRow1_2_1_2 := by rfl
def stateRow1_2_1_3 : List State := [(1,3),(4,2),(5,3),(8,5),(6,5),(0,4),(3,4),(6,3),(7,2),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(7,3),(4,2),(5,3),(8,5),(1,0),(1,2),(7,4),(6,3),(7,2)]
def patch1_2_1_3 : Patch := literalDomain.zip stateRow1_2_1_3
theorem patch_states1_2_1_3 : patch1_2_1_3.map Prod.snd = stateRow1_2_1_3 := by rfl
def stateRow1_2_1_4 : List State := [(6,3),(7,2),(7,4),(6,3),(0,2),(1,1),(4,1),(0,2),(1,1),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(1,2),(7,4),(6,3),(7,2)]
def patch1_2_1_4 : Patch := literalDomain.zip stateRow1_2_1_4
theorem patch_states1_2_1_4 : patch1_2_1_4.map Prod.snd = stateRow1_2_1_4 := by rfl
def stateRow1_2_1_5 : List State := [(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(3,1),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(1,2),(7,4),(6,3),(7,2)]
def patch1_2_1_5 : Patch := literalDomain.zip stateRow1_2_1_5
theorem patch_states1_2_1_5 : patch1_2_1_5.map Prod.snd = stateRow1_2_1_5 := by rfl
def stateRow1_2_1_7 : List State := [(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(0,3),(5,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(8,2),(7,1),(7,5),(0,3),(8,1),(6,5),(0,4),(7,3),(4,2),(5,3),(8,5),(7,0),(1,2),(7,4),(6,3),(7,2)]
def patch1_2_1_7 : Patch := literalDomain.zip stateRow1_2_1_7
theorem patch_states1_2_1_7 : patch1_2_1_7.map Prod.snd = stateRow1_2_1_7 := by rfl
def stateRow1_2_1_10 : List State := [(6,3),(7,2),(7,4),(6,3),(0,2),(1,1),(4,1),(0,2),(1,1),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(6,2),(7,4),(6,3),(7,2)]
def patch1_2_1_10 : Patch := literalDomain.zip stateRow1_2_1_10
theorem patch_states1_2_1_10 : patch1_2_1_10.map Prod.snd = stateRow1_2_1_10 := by rfl
def stateRow1_2_1_11 : List State := [(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(3,1),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(6,2),(7,4),(6,3),(7,2)]
def patch1_2_1_11 : Patch := literalDomain.zip stateRow1_2_1_11
theorem patch_states1_2_1_11 : patch1_2_1_11.map Prod.snd = stateRow1_2_1_11 := by rfl
def final1_2_1 : List Patch := [patch1_2_1_0, patch1_2_1_1, patch1_2_1_2, patch1_2_1_3, patch1_2_1_4, patch1_2_1_5, patch1_2_1_7, patch1_2_1_10, patch1_2_1_11]
def stateRows1_2_1 : List (List State) := [stateRow1_2_1_0, stateRow1_2_1_1, stateRow1_2_1_2, stateRow1_2_1_3, stateRow1_2_1_4, stateRow1_2_1_5, stateRow1_2_1_7, stateRow1_2_1_10, stateRow1_2_1_11]
theorem stateRows_eq1_2_1 : stateRows1_2_1 = final1_2_1.map (List.map Prod.snd) := by
  simp only [stateRows1_2_1, final1_2_1, List.map_cons, List.map_nil, patch_states1_2_1_0, patch_states1_2_1_1, patch_states1_2_1_2, patch_states1_2_1_3, patch_states1_2_1_4, patch_states1_2_1_5, patch_states1_2_1_7, patch_states1_2_1_10, patch_states1_2_1_11]
theorem final_states1_2_1 : final1_2_1 = stateRows1_2_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
