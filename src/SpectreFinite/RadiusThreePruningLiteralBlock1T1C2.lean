module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_1_2_0 : List State := [(6,1),(8,1),(6,5),(0,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,2),(7,4),(6,3),(7,2),(7,4),(1,3),(6,1),(4,1),(0,2),(1,1),(8,1),(6,5),(0,4),(7,3),(5,2),(8,0),(8,3),(5,5),(7,0),(6,2),(8,4),(1,4),(0,5),(4,4),(7,1),(7,5),(6,0),(7,1)]
def patch1_1_2_0 : Patch := literalDomain.zip stateRow1_1_2_0
theorem patch_states1_1_2_0 : patch1_1_2_0.map Prod.snd = stateRow1_1_2_0 := by rfl
def stateRow1_1_2_1 : List State := [(6,1),(8,1),(6,5),(0,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,2),(7,4),(6,3),(7,2),(7,4),(6,3),(6,1),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(7,3),(5,2),(8,0),(7,3),(5,2),(5,0),(6,2),(8,4),(6,4),(1,2),(8,4),(7,1),(7,5),(0,3),(8,1)]
def patch1_1_2_1 : Patch := literalDomain.zip stateRow1_1_2_1
theorem patch_states1_1_2_1 : patch1_1_2_1.map Prod.snd = stateRow1_1_2_1 := by rfl
def final1_1_2 : List Patch := [patch1_1_2_0, patch1_1_2_1]
def stateRows1_1_2 : List (List State) := [stateRow1_1_2_0, stateRow1_1_2_1]
theorem stateRows_eq1_1_2 : stateRows1_1_2 = final1_1_2.map (List.map Prod.snd) := by
  simp only [stateRows1_1_2, final1_1_2, List.map_cons, List.map_nil, patch_states1_1_2_0, patch_states1_1_2_1]
theorem final_states1_1_2 : final1_1_2 = stateRows1_1_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
