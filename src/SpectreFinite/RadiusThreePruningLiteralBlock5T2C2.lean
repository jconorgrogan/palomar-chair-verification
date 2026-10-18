module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_2_2_0 : List State := [(8,5),(7,0),(8,3),(8,5),(6,3),(7,2),(7,4),(6,3),(7,2),(0,2),(1,1),(4,1),(0,2),(1,1),(8,1),(3,2),(4,0),(7,3),(5,2),(8,0),(8,3),(5,5),(5,1),(0,1),(6,2),(8,4),(1,4),(0,5),(8,5),(1,0),(7,1),(7,5),(6,0),(8,2),(8,0),(7,3),(8,2)]
def patch5_2_2_0 : Patch := literalDomain.zip stateRow5_2_2_0
theorem patch_states5_2_2_0 : patch5_2_2_0.map Prod.snd = stateRow5_2_2_0 := by rfl
def final5_2_2 : List Patch := [patch5_2_2_0]
def stateRows5_2_2 : List (List State) := [stateRow5_2_2_0]
theorem stateRows_eq5_2_2 : stateRows5_2_2 = final5_2_2.map (List.map Prod.snd) := by
  simp only [stateRows5_2_2, final5_2_2, List.map_cons, List.map_nil, patch_states5_2_2_0]
theorem final_states5_2_2 : final5_2_2 = stateRows5_2_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
