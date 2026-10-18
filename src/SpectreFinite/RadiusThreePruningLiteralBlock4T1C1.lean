module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_1_1_0 : List State := [(8,1),(1,5),(6,1),(8,1),(5,3),(8,5),(7,0),(8,3),(8,5),(3,4),(6,3),(7,2),(7,4),(6,3),(7,2),(2,3),(0,2),(1,1),(4,1),(0,2),(1,1),(8,1),(1,2),(4,0),(7,3),(5,2),(8,0),(8,3),(5,1),(0,1),(6,2),(8,4),(1,4),(8,5),(1,0),(7,1),(7,5)]
def patch4_1_1_0 : Patch := literalDomain.zip stateRow4_1_1_0
theorem patch_states4_1_1_0 : patch4_1_1_0.map Prod.snd = stateRow4_1_1_0 := by rfl
def stateRow4_1_1_1 : List State := [(8,1),(1,5),(6,1),(8,1),(5,3),(8,5),(7,0),(8,3),(8,5),(3,4),(6,3),(7,2),(7,4),(6,3),(7,2),(2,3),(0,2),(1,1),(4,1),(0,2),(1,1),(4,1),(1,2),(4,0),(7,3),(5,2),(8,0),(7,3),(5,1),(0,1),(6,2),(8,4),(6,4),(8,5),(1,0),(7,1),(7,5)]
def patch4_1_1_1 : Patch := literalDomain.zip stateRow4_1_1_1
theorem patch_states4_1_1_1 : patch4_1_1_1.map Prod.snd = stateRow4_1_1_1 := by rfl
def stateRow4_1_1_2 : List State := [(8,1),(6,5),(0,4),(5,4),(5,3),(8,5),(7,0),(4,3),(7,5),(3,4),(6,3),(7,2),(7,4),(6,3),(2,2),(2,3),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(1,2),(4,0),(7,3),(5,2),(5,0),(4,5),(5,1),(0,1),(6,2),(8,4),(0,0),(8,5),(1,0),(7,1),(1,5)]
def patch4_1_1_2 : Patch := literalDomain.zip stateRow4_1_1_2
theorem patch_states4_1_1_2 : patch4_1_1_2.map Prod.snd = stateRow4_1_1_2 := by rfl
def stateRow4_1_1_3 : List State := [(8,1),(1,5),(6,1),(5,1),(5,3),(8,5),(7,0),(8,3),(8,5),(7,4),(6,3),(7,2),(7,4),(6,3),(7,2),(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(5,1),(3,2),(4,0),(7,3),(5,2),(8,0),(8,3),(5,1),(0,1),(6,2),(8,4),(1,4),(8,5),(1,0),(7,1),(7,5)]
def patch4_1_1_3 : Patch := literalDomain.zip stateRow4_1_1_3
theorem patch_states4_1_1_3 : patch4_1_1_3.map Prod.snd = stateRow4_1_1_3 := by rfl
def stateRow4_1_1_4 : List State := [(8,1),(1,5),(6,1),(8,1),(5,3),(8,5),(7,0),(8,3),(8,5),(7,4),(6,3),(7,2),(7,4),(6,3),(7,2),(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(8,1),(3,2),(4,0),(7,3),(5,2),(8,0),(8,3),(5,1),(0,1),(6,2),(8,4),(1,4),(8,5),(1,0),(7,1),(7,5)]
def patch4_1_1_4 : Patch := literalDomain.zip stateRow4_1_1_4
theorem patch_states4_1_1_4 : patch4_1_1_4.map Prod.snd = stateRow4_1_1_4 := by rfl
def stateRow4_1_1_5 : List State := [(8,1),(1,5),(6,1),(8,1),(5,3),(8,5),(7,0),(8,3),(8,5),(7,4),(6,3),(7,2),(7,4),(6,3),(7,2),(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(4,1),(3,2),(4,0),(7,3),(5,2),(8,0),(7,3),(5,1),(0,1),(6,2),(8,4),(6,4),(8,5),(1,0),(7,1),(7,5)]
def patch4_1_1_5 : Patch := literalDomain.zip stateRow4_1_1_5
theorem patch_states4_1_1_5 : patch4_1_1_5.map Prod.snd = stateRow4_1_1_5 := by rfl
def stateRow4_1_1_6 : List State := [(8,1),(6,5),(0,4),(5,4),(5,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(3,2),(4,0),(7,3),(5,2),(5,0),(4,5),(5,1),(0,1),(6,2),(8,4),(0,0),(8,5),(1,0),(7,1),(1,5)]
def patch4_1_1_6 : Patch := literalDomain.zip stateRow4_1_1_6
theorem patch_states4_1_1_6 : patch4_1_1_6.map Prod.snd = stateRow4_1_1_6 := by rfl
def stateRow4_1_1_7 : List State := [(8,1),(6,5),(0,4),(5,4),(5,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(5,4),(6,4),(1,2),(8,4),(0,0),(7,5),(0,3),(8,1),(1,5)]
def patch4_1_1_7 : Patch := literalDomain.zip stateRow4_1_1_7
theorem patch_states4_1_1_7 : patch4_1_1_7.map Prod.snd = stateRow4_1_1_7 := by rfl
def stateRow4_1_1_8 : List State := [(8,1),(6,5),(0,4),(5,4),(5,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(8,4),(6,4),(1,2),(8,4),(0,0),(7,5),(0,3),(8,1),(1,5)]
def patch4_1_1_8 : Patch := literalDomain.zip stateRow4_1_1_8
theorem patch_states4_1_1_8 : patch4_1_1_8.map Prod.snd = stateRow4_1_1_8 := by rfl
def stateRow4_1_1_9 : List State := [(8,1),(6,5),(0,4),(5,4),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(8,4),(6,4),(1,2),(8,4),(0,0),(7,5),(0,3),(8,1),(1,5)]
def patch4_1_1_9 : Patch := literalDomain.zip stateRow4_1_1_9
theorem patch_states4_1_1_9 : patch4_1_1_9.map Prod.snd = stateRow4_1_1_9 := by rfl
def final4_1_1 : List Patch := [patch4_1_1_0, patch4_1_1_1, patch4_1_1_2, patch4_1_1_3, patch4_1_1_4, patch4_1_1_5, patch4_1_1_6, patch4_1_1_7, patch4_1_1_8, patch4_1_1_9]
def stateRows4_1_1 : List (List State) := [stateRow4_1_1_0, stateRow4_1_1_1, stateRow4_1_1_2, stateRow4_1_1_3, stateRow4_1_1_4, stateRow4_1_1_5, stateRow4_1_1_6, stateRow4_1_1_7, stateRow4_1_1_8, stateRow4_1_1_9]
theorem stateRows_eq4_1_1 : stateRows4_1_1 = final4_1_1.map (List.map Prod.snd) := by
  simp only [stateRows4_1_1, final4_1_1, List.map_cons, List.map_nil, patch_states4_1_1_0, patch_states4_1_1_1, patch_states4_1_1_2, patch_states4_1_1_3, patch_states4_1_1_4, patch_states4_1_1_5, patch_states4_1_1_6, patch_states4_1_1_7, patch_states4_1_1_8, patch_states4_1_1_9]
theorem final_states4_1_1 : final4_1_1 = stateRows4_1_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
