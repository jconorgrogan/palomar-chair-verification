module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_3_1_0 : List State := [(0,2),(1,1),(4,1),(0,2),(5,2),(8,0),(7,3),(5,2),(5,0),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(0,1),(6,2),(7,4),(6,3),(7,2),(1,0),(2,1),(0,2),(1,1)]
def patch0_3_1_0 : Patch := literalDomain.zip stateRow0_3_1_0
theorem patch_states0_3_1_0 : patch0_3_1_0.map Prod.snd = stateRow0_3_1_0 := by rfl
def stateRow0_3_1_1 : List State := [(6,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2),(5,0),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(0,1),(6,2),(7,4),(6,3),(7,2),(1,0),(2,1),(0,2),(1,1)]
def patch0_3_1_1 : Patch := literalDomain.zip stateRow0_3_1_1
theorem patch_states0_3_1_1 : patch0_3_1_1.map Prod.snd = stateRow0_3_1_1 := by rfl
def stateRow0_3_1_3 : List State := [(6,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(1,0),(7,1),(7,5),(0,3),(8,1),(6,5),(0,4),(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(6,4),(1,2),(7,4),(6,3),(7,2),(0,3),(4,1),(0,2),(1,1)]
def patch0_3_1_3 : Patch := literalDomain.zip stateRow0_3_1_3
theorem patch_states0_3_1_3 : patch0_3_1_3.map Prod.snd = stateRow0_3_1_3 := by rfl
def stateRow0_3_1_4 : List State := [(0,2),(1,1),(4,1),(0,2),(5,2),(8,0),(7,3),(5,2),(5,0),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(6,4),(1,2),(7,4),(6,3),(7,2),(0,3),(4,1),(0,2),(1,1)]
def patch0_3_1_4 : Patch := literalDomain.zip stateRow0_3_1_4
theorem patch_states0_3_1_4 : patch0_3_1_4.map Prod.snd = stateRow0_3_1_4 := by rfl
def stateRow0_3_1_5 : List State := [(6,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2),(5,0),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(6,4),(1,2),(7,4),(6,3),(7,2),(0,3),(4,1),(0,2),(1,1)]
def patch0_3_1_5 : Patch := literalDomain.zip stateRow0_3_1_5
theorem patch_states0_3_1_5 : patch0_3_1_5.map Prod.snd = stateRow0_3_1_5 := by rfl
def stateRow0_3_1_6 : List State := [(6,0),(7,1),(7,5),(0,3),(8,2),(8,0),(7,3),(4,2),(5,3),(0,4),(5,4),(6,4),(1,2),(7,4),(1,3),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(6,5),(0,4),(1,4),(0,5),(4,4),(3,0),(2,5),(6,0),(7,1)]
def patch0_3_1_6 : Patch := literalDomain.zip stateRow0_3_1_6
theorem patch_states0_3_1_6 : patch0_3_1_6.map Prod.snd = stateRow0_3_1_6 := by rfl
def stateRow0_3_1_7 : List State := [(0,2),(1,1),(4,1),(0,2),(5,2),(8,0),(7,3),(5,2),(5,0),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(6,5),(0,4),(1,4),(0,5),(4,4),(3,0),(2,5),(6,0),(7,1)]
def patch0_3_1_7 : Patch := literalDomain.zip stateRow0_3_1_7
theorem patch_states0_3_1_7 : patch0_3_1_7.map Prod.snd = stateRow0_3_1_7 := by rfl
def stateRow0_3_1_8 : List State := [(1,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2),(5,0),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(6,5),(0,4),(1,4),(0,5),(4,4),(3,0),(2,5),(6,0),(7,1)]
def patch0_3_1_8 : Patch := literalDomain.zip stateRow0_3_1_8
theorem patch_states0_3_1_8 : patch0_3_1_8.map Prod.snd = stateRow0_3_1_8 := by rfl
def stateRow0_3_1_9 : List State := [(6,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2),(5,0),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(6,5),(0,4),(1,4),(0,5),(4,4),(3,0),(2,5),(6,0),(7,1)]
def patch0_3_1_9 : Patch := literalDomain.zip stateRow0_3_1_9
theorem patch_states0_3_1_9 : patch0_3_1_9.map Prod.snd = stateRow0_3_1_9 := by rfl
def final0_3_1 : List Patch := [patch0_3_1_0, patch0_3_1_1, patch0_3_1_3, patch0_3_1_4, patch0_3_1_5, patch0_3_1_6, patch0_3_1_7, patch0_3_1_8, patch0_3_1_9]
def stateRows0_3_1 : List (List State) := [stateRow0_3_1_0, stateRow0_3_1_1, stateRow0_3_1_3, stateRow0_3_1_4, stateRow0_3_1_5, stateRow0_3_1_6, stateRow0_3_1_7, stateRow0_3_1_8, stateRow0_3_1_9]
theorem stateRows_eq0_3_1 : stateRows0_3_1 = final0_3_1.map (List.map Prod.snd) := by
  simp only [stateRows0_3_1, final0_3_1, List.map_cons, List.map_nil, patch_states0_3_1_0, patch_states0_3_1_1, patch_states0_3_1_3, patch_states0_3_1_4, patch_states0_3_1_5, patch_states0_3_1_6, patch_states0_3_1_7, patch_states0_3_1_8, patch_states0_3_1_9]
theorem final_states0_3_1 : final0_3_1 = stateRows0_3_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
