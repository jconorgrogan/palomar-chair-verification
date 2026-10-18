module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_4_0_0 : List State := [(7,2),(7,4),(1,3),(4,2),(1,1),(8,1),(6,5),(0,4),(3,4),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(5,4),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(8,2),(8,0),(7,3),(4,2),(5,3),(5,4),(6,4),(1,2),(7,4)]
def patch4_4_0_0 : Patch := literalDomain.zip stateRow4_4_0_0
theorem patch_states4_4_0_0 : patch4_4_0_0.map Prod.snd = stateRow4_4_0_0 := by rfl
def stateRow4_4_0_1 : List State := [(7,2),(7,4),(1,3),(4,2),(1,1),(8,1),(6,5),(0,4),(3,4),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(8,4),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,4),(6,4),(1,2),(7,4)]
def patch4_4_0_1 : Patch := literalDomain.zip stateRow4_4_0_1
theorem patch_states4_4_0_1 : patch4_4_0_1.map Prod.snd = stateRow4_4_0_1 := by rfl
def stateRow4_4_0_2 : List State := [(7,2),(7,4),(1,3),(4,2),(6,1),(8,1),(6,5),(0,4),(3,4),(7,0),(8,3),(5,5),(7,0),(2,3),(0,2),(4,4),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,4),(6,4),(1,2),(7,4)]
def patch4_4_0_2 : Patch := literalDomain.zip stateRow4_4_0_2
theorem patch_states4_4_0_2 : patch4_4_0_2.map Prod.snd = stateRow4_4_0_2 := by rfl
def stateRow4_4_0_4 : List State := [(7,2),(4,0),(7,3),(4,2),(1,1),(5,1),(0,1),(6,2),(7,4),(8,0),(8,3),(5,5),(1,0),(2,1),(0,2),(5,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(5,4),(0,0),(7,2),(7,4)]
def patch4_4_0_4 : Patch := literalDomain.zip stateRow4_4_0_4
theorem patch_states4_4_0_4 : patch4_4_0_4.map Prod.snd = stateRow4_4_0_4 := by rfl
def stateRow4_4_0_5 : List State := [(7,2),(4,0),(7,3),(4,2),(1,1),(5,1),(0,1),(6,2),(7,4),(8,0),(8,3),(5,5),(1,0),(2,1),(0,2),(8,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,4),(0,0),(7,2),(7,4)]
def patch4_4_0_5 : Patch := literalDomain.zip stateRow4_4_0_5
theorem patch_states4_4_0_5 : patch4_4_0_5.map Prod.snd = stateRow4_4_0_5 := by rfl
def stateRow4_4_0_6 : List State := [(7,2),(4,0),(7,3),(4,2),(6,1),(5,1),(0,1),(6,2),(7,4),(7,0),(8,3),(5,5),(1,0),(2,1),(0,2),(4,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,4),(0,0),(7,2),(7,4)]
def patch4_4_0_6 : Patch := literalDomain.zip stateRow4_4_0_6
theorem patch_states4_4_0_6 : patch4_4_0_6.map Prod.snd = stateRow4_4_0_6 := by rfl
def stateRow4_4_0_7 : List State := [(7,2),(7,4),(1,3),(4,2),(1,1),(8,1),(6,5),(0,4),(1,4),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(5,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(5,4),(0,0),(7,2),(7,4)]
def patch4_4_0_7 : Patch := literalDomain.zip stateRow4_4_0_7
theorem patch_states4_4_0_7 : patch4_4_0_7.map Prod.snd = stateRow4_4_0_7 := by rfl
def stateRow4_4_0_8 : List State := [(7,2),(7,4),(1,3),(4,2),(1,1),(8,1),(6,5),(0,4),(1,4),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(8,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,4),(0,0),(7,2),(7,4)]
def patch4_4_0_8 : Patch := literalDomain.zip stateRow4_4_0_8
theorem patch_states4_4_0_8 : patch4_4_0_8.map Prod.snd = stateRow4_4_0_8 := by rfl
def stateRow4_4_0_9 : List State := [(7,2),(7,4),(1,3),(4,2),(6,1),(8,1),(6,5),(0,4),(1,4),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(8,2),(5,0),(4,5),(7,0),(8,3),(8,4),(0,0),(7,2),(7,4)]
def patch4_4_0_9 : Patch := literalDomain.zip stateRow4_4_0_9
theorem patch_states4_4_0_9 : patch4_4_0_9.map Prod.snd = stateRow4_4_0_9 := by rfl
def stateRow4_4_0_11 : List State := [(7,2),(7,4),(1,3),(8,2),(1,1),(8,1),(6,5),(0,4),(5,4),(8,0),(8,3),(5,5),(7,0),(4,3),(1,5),(5,4),(1,4),(0,5),(4,4),(1,4),(0,5),(2,0),(7,5),(6,0),(7,1),(7,5),(6,0),(3,1),(8,2),(8,0),(7,3),(8,2),(5,0),(5,4),(6,4),(1,2),(8,4)]
def patch4_4_0_11 : Patch := literalDomain.zip stateRow4_4_0_11
theorem patch_states4_4_0_11 : patch4_4_0_11.map Prod.snd = stateRow4_4_0_11 := by rfl
def final4_4_0 : List Patch := [patch4_4_0_0, patch4_4_0_1, patch4_4_0_2, patch4_4_0_4, patch4_4_0_5, patch4_4_0_6, patch4_4_0_7, patch4_4_0_8, patch4_4_0_9, patch4_4_0_11]
def stateRows4_4_0 : List (List State) := [stateRow4_4_0_0, stateRow4_4_0_1, stateRow4_4_0_2, stateRow4_4_0_4, stateRow4_4_0_5, stateRow4_4_0_6, stateRow4_4_0_7, stateRow4_4_0_8, stateRow4_4_0_9, stateRow4_4_0_11]
theorem stateRows_eq4_4_0 : stateRows4_4_0 = final4_4_0.map (List.map Prod.snd) := by
  simp only [stateRows4_4_0, final4_4_0, List.map_cons, List.map_nil, patch_states4_4_0_0, patch_states4_4_0_1, patch_states4_4_0_2, patch_states4_4_0_4, patch_states4_4_0_5, patch_states4_4_0_6, patch_states4_4_0_7, patch_states4_4_0_8, patch_states4_4_0_9, patch_states4_4_0_11]
theorem final_states4_4_0 : final4_4_0 = stateRows4_4_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
