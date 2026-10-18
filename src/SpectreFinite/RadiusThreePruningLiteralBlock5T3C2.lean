module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_3_2_0 : List State := [(8,0),(7,3),(8,2),(5,0),(8,4),(6,4),(1,2),(8,4),(0,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(6,4),(1,2),(7,4),(6,3),(7,2),(7,4),(0,3),(4,1),(0,2),(1,1),(8,1),(3,3),(5,2),(8,0),(8,3)]
def patch5_3_2_0 : Patch := literalDomain.zip stateRow5_3_2_0
theorem patch_states5_3_2_0 : patch5_3_2_0.map Prod.snd = stateRow5_3_2_0 := by rfl
def final5_3_2 : List Patch := [patch5_3_2_0]
def stateRows5_3_2 : List (List State) := [stateRow5_3_2_0]
theorem stateRows_eq5_3_2 : stateRows5_3_2 = final5_3_2.map (List.map Prod.snd) := by
  simp only [stateRows5_3_2, final5_3_2, List.map_cons, List.map_nil, patch_states5_3_2_0]
theorem final_states5_3_2 : final5_3_2 = stateRows5_3_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
