module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_2_2_0 : List State := [(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(7,1),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(6,2),(7,4),(6,3),(7,2)]
def patch1_2_2_0 : Patch := literalDomain.zip stateRow1_2_2_0
theorem patch_states1_2_2_0 : patch1_2_2_0.map Prod.snd = stateRow1_2_2_0 := by rfl
def stateRow1_2_2_1 : List State := [(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(0,3),(5,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(8,2),(7,1),(7,5),(0,3),(8,1),(6,5),(0,4),(7,3),(4,2),(5,3),(8,5),(7,0),(6,2),(7,4),(6,3),(7,2)]
def patch1_2_2_1 : Patch := literalDomain.zip stateRow1_2_2_1
theorem patch_states1_2_2_1 : patch1_2_2_1.map Prod.snd = stateRow1_2_2_1 := by rfl
def final1_2_2 : List Patch := [patch1_2_2_0, patch1_2_2_1]
def stateRows1_2_2 : List (List State) := [stateRow1_2_2_0, stateRow1_2_2_1]
theorem stateRows_eq1_2_2 : stateRows1_2_2 = final1_2_2.map (List.map Prod.snd) := by
  simp only [stateRows1_2_2, final1_2_2, List.map_cons, List.map_nil, patch_states1_2_2_0, patch_states1_2_2_1]
theorem final_states1_2_2 : final1_2_2 = stateRows1_2_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
