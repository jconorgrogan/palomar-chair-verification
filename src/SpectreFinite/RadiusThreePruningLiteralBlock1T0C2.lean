module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_0_2_0 : List State := [(6,0),(7,1),(7,5),(6,0),(7,2),(4,0),(7,3),(8,2),(8,0),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(6,5),(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(7,5),(0,3)]
def patch1_0_2_0 : Patch := literalDomain.zip stateRow1_0_2_0
theorem patch_states1_0_2_0 : patch1_0_2_0.map Prod.snd = stateRow1_0_2_0 := by rfl
def stateRow1_0_2_1 : List State := [(6,0),(7,1),(7,5),(6,0),(7,2),(4,0),(7,3),(8,2),(8,0),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(0,2),(1,1),(5,1),(0,1),(6,2),(8,0),(8,3),(5,5),(1,0)]
def patch1_0_2_1 : Patch := literalDomain.zip stateRow1_0_2_1
theorem patch_states1_0_2_1 : patch1_0_2_1.map Prod.snd = stateRow1_0_2_1 := by rfl
def final1_0_2 : List Patch := [patch1_0_2_0, patch1_0_2_1]
def stateRows1_0_2 : List (List State) := [stateRow1_0_2_0, stateRow1_0_2_1]
theorem stateRows_eq1_0_2 : stateRows1_0_2 = final1_0_2.map (List.map Prod.snd) := by
  simp only [stateRows1_0_2, final1_0_2, List.map_cons, List.map_nil, patch_states1_0_2_0, patch_states1_0_2_1]
theorem final_states1_0_2 : final1_0_2 = stateRows1_0_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
