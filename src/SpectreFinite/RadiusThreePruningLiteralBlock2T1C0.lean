module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_1_0_0 : List State := [(7,1),(7,5),(0,3),(8,1),(4,0),(7,3),(4,2),(5,3),(8,5),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(4,1),(0,5),(4,4),(0,0),(3,2),(4,0),(7,3),(7,1),(1,5),(6,1),(5,1),(0,1),(4,5),(7,0),(8,3),(8,5)]
def patch2_1_0_0 : Patch := literalDomain.zip stateRow2_1_0_0
theorem patch_states2_1_0_0 : patch2_1_0_0.map Prod.snd = stateRow2_1_0_0 := by rfl
def final2_1_0 : List Patch := [patch2_1_0_0]
def stateRows2_1_0 : List (List State) := [stateRow2_1_0_0]
theorem stateRows_eq2_1_0 : stateRows2_1_0 = final2_1_0.map (List.map Prod.snd) := by
  simp only [stateRows2_1_0, final2_1_0, List.map_cons, List.map_nil, patch_states2_1_0_0]
theorem final_states2_1_0 : final2_1_0 = stateRows2_1_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
