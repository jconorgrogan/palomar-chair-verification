module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_3_0_0 : List State := [(1,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(1,1),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(6,0),(7,1),(6,5),(0,4),(5,4),(5,0),(4,5),(7,0),(4,3)]
def patch0_3_0_0 : Patch := literalDomain.zip stateRow0_3_0_0
theorem patch_states0_3_0_0 : patch0_3_0_0.map Prod.snd = stateRow0_3_0_0 := by rfl
def stateRow0_3_0_1 : List State := [(6,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(1,1),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(6,0),(7,1),(6,5),(0,4),(5,4),(5,0),(4,5),(7,0),(4,3)]
def patch0_3_0_1 : Patch := literalDomain.zip stateRow0_3_0_1
theorem patch_states0_3_0_1 : patch0_3_0_1.map Prod.snd = stateRow0_3_0_1 := by rfl
def stateRow0_3_0_2 : List State := [(1,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(0,2),(1,1),(0,1),(6,2),(8,4),(5,0),(4,5),(1,0),(7,1)]
def patch0_3_0_2 : Patch := literalDomain.zip stateRow0_3_0_2
theorem patch_states0_3_0_2 : patch0_3_0_2.map Prod.snd = stateRow0_3_0_2 := by rfl
def stateRow0_3_0_3 : List State := [(6,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(0,2),(1,1),(0,1),(6,2),(8,4),(5,0),(4,5),(1,0),(7,1)]
def patch0_3_0_3 : Patch := literalDomain.zip stateRow0_3_0_3
theorem patch_states0_3_0_3 : patch0_3_0_3.map Prod.snd = stateRow0_3_0_3 := by rfl
def stateRow0_3_0_5 : List State := [(6,5),(0,4),(3,4),(6,3),(5,5),(7,0),(2,3),(0,2),(1,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,4),(1,2),(7,4),(1,3),(8,2),(0,3),(8,1),(6,5),(0,4)]
def patch0_3_0_5 : Patch := literalDomain.zip stateRow0_3_0_5
theorem patch_states0_3_0_5 : patch0_3_0_5.map Prod.snd = stateRow0_3_0_5 := by rfl
def stateRow0_3_0_6 : List State := [(6,5),(0,4),(3,4),(6,3),(5,5),(7,0),(2,3),(0,2),(1,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,4),(1,2),(7,4),(6,3),(7,2),(0,3),(4,1),(0,2),(1,1)]
def patch0_3_0_6 : Patch := literalDomain.zip stateRow0_3_0_6
theorem patch_states0_3_0_6 : patch0_3_0_6.map Prod.snd = stateRow0_3_0_6 := by rfl
def stateRow0_3_0_7 : List State := [(6,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(0,4),(5,4),(6,4),(1,2),(7,4),(1,3),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,5),(0,4),(3,4),(6,3),(7,2),(7,0),(2,3),(0,2),(1,1)]
def patch0_3_0_7 : Patch := literalDomain.zip stateRow0_3_0_7
theorem patch_states0_3_0_7 : patch0_3_0_7.map Prod.snd = stateRow0_3_0_7 := by rfl
def stateRow0_3_0_8 : List State := [(0,2),(1,1),(4,1),(0,2),(5,2),(8,0),(7,3),(5,2),(5,0),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,5),(0,4),(3,4),(6,3),(7,2),(7,0),(2,3),(0,2),(1,1)]
def patch0_3_0_8 : Patch := literalDomain.zip stateRow0_3_0_8
theorem patch_states0_3_0_8 : patch0_3_0_8.map Prod.snd = stateRow0_3_0_8 := by rfl
def stateRow0_3_0_9 : List State := [(1,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2),(5,0),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,5),(0,4),(3,4),(6,3),(7,2),(7,0),(2,3),(0,2),(1,1)]
def patch0_3_0_9 : Patch := literalDomain.zip stateRow0_3_0_9
theorem patch_states0_3_0_9 : patch0_3_0_9.map Prod.snd = stateRow0_3_0_9 := by rfl
def stateRow0_3_0_10 : List State := [(6,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2),(5,0),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,5),(0,4),(3,4),(6,3),(7,2),(7,0),(2,3),(0,2),(1,1)]
def patch0_3_0_10 : Patch := literalDomain.zip stateRow0_3_0_10
theorem patch_states0_3_0_10 : patch0_3_0_10.map Prod.snd = stateRow0_3_0_10 := by rfl
def stateRow0_3_0_11 : List State := [(6,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(1,0),(7,1),(7,5),(0,3),(8,1),(6,5),(0,4),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(0,1),(6,2),(7,4),(6,3),(7,2),(1,0),(2,1),(0,2),(1,1)]
def patch0_3_0_11 : Patch := literalDomain.zip stateRow0_3_0_11
theorem patch_states0_3_0_11 : patch0_3_0_11.map Prod.snd = stateRow0_3_0_11 := by rfl
def final0_3_0 : List Patch := [patch0_3_0_0, patch0_3_0_1, patch0_3_0_2, patch0_3_0_3, patch0_3_0_5, patch0_3_0_6, patch0_3_0_7, patch0_3_0_8, patch0_3_0_9, patch0_3_0_10, patch0_3_0_11]
def stateRows0_3_0 : List (List State) := [stateRow0_3_0_0, stateRow0_3_0_1, stateRow0_3_0_2, stateRow0_3_0_3, stateRow0_3_0_5, stateRow0_3_0_6, stateRow0_3_0_7, stateRow0_3_0_8, stateRow0_3_0_9, stateRow0_3_0_10, stateRow0_3_0_11]
theorem stateRows_eq0_3_0 : stateRows0_3_0 = final0_3_0.map (List.map Prod.snd) := by
  simp only [stateRows0_3_0, final0_3_0, List.map_cons, List.map_nil, patch_states0_3_0_0, patch_states0_3_0_1, patch_states0_3_0_2, patch_states0_3_0_3, patch_states0_3_0_5, patch_states0_3_0_6, patch_states0_3_0_7, patch_states0_3_0_8, patch_states0_3_0_9, patch_states0_3_0_10, patch_states0_3_0_11]
theorem final_states0_3_0 : final0_3_0 = stateRows0_3_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
