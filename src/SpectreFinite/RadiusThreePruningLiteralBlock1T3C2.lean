module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_3_2_0 : List State := [(0,0),(7,2),(4,0),(7,3),(1,5),(6,1),(5,1),(0,1),(6,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(8,3),(8,5),(7,0),(4,3),(7,5),(6,3),(7,2),(7,4),(6,3)]
def patch1_3_2_0 : Patch := literalDomain.zip stateRow1_3_2_0
theorem patch_states1_3_2_0 : patch1_3_2_0.map Prod.snd = stateRow1_3_2_0 := by rfl
def stateRow1_3_2_1 : List State := [(1,3),(5,2),(8,0),(8,3),(6,5),(0,4),(5,4),(1,4),(0,5),(4,5),(7,0),(4,3),(7,5),(6,0),(7,1),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(8,3),(8,5),(7,0),(4,3),(7,5),(6,3),(7,2),(7,4),(6,3)]
def patch1_3_2_1 : Patch := literalDomain.zip stateRow1_3_2_1
theorem patch_states1_3_2_1 : patch1_3_2_1.map Prod.snd = stateRow1_3_2_1 := by rfl
def final1_3_2 : List Patch := [patch1_3_2_0, patch1_3_2_1]
def stateRows1_3_2 : List (List State) := [stateRow1_3_2_0, stateRow1_3_2_1]
theorem stateRows_eq1_3_2 : stateRows1_3_2 = final1_3_2.map (List.map Prod.snd) := by
  simp only [stateRows1_3_2, final1_3_2, List.map_cons, List.map_nil, patch_states1_3_2_0, patch_states1_3_2_1]
theorem final_states1_3_2 : final1_3_2 = stateRows1_3_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
