module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_5_2_0 : List State := [(7,5),(6,0),(7,1),(6,5),(7,3),(8,2),(5,0),(4,5),(7,0),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(7,4),(6,3),(7,2),(7,4),(6,3),(0,2),(1,1),(4,1),(0,2)]
def patch1_5_2_0 : Patch := literalDomain.zip stateRow1_5_2_0
theorem patch_states1_5_2_0 : patch1_5_2_0.map Prod.snd = stateRow1_5_2_0 := by rfl
def stateRow1_5_2_1 : List State := [(7,5),(6,0),(7,1),(6,5),(7,3),(8,2),(5,0),(4,5),(7,0),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4),(8,5),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(5,4),(0,0),(7,2),(7,4),(6,3),(1,5),(6,1),(4,1),(0,2)]
def patch1_5_2_1 : Patch := literalDomain.zip stateRow1_5_2_1
theorem patch_states1_5_2_1 : patch1_5_2_1.map Prod.snd = stateRow1_5_2_1 := by rfl
def final1_5_2 : List Patch := [patch1_5_2_0, patch1_5_2_1]
def stateRows1_5_2 : List (List State) := [stateRow1_5_2_0, stateRow1_5_2_1]
theorem stateRows_eq1_5_2 : stateRows1_5_2 = final1_5_2.map (List.map Prod.snd) := by
  simp only [stateRows1_5_2, final1_5_2, List.map_cons, List.map_nil, patch_states1_5_2_0, patch_states1_5_2_1]
theorem final_states1_5_2 : final1_5_2 = stateRows1_5_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
