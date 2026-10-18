module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_2_0_0 : List State := [(8,2),(8,0),(7,3),(4,2),(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(7,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(5,2),(5,0),(4,5),(1,0),(7,1),(8,4),(0,0),(7,2),(4,0)]
def patch2_2_0_0 : Patch := literalDomain.zip stateRow2_2_0_0
theorem patch_states2_2_0_0 : patch2_2_0_0.map Prod.snd = stateRow2_2_0_0 := by rfl
def final2_2_0 : List Patch := [patch2_2_0_0]
def stateRows2_2_0 : List (List State) := [stateRow2_2_0_0]
theorem stateRows_eq2_2_0 : stateRows2_2_0 = final2_2_0.map (List.map Prod.snd) := by
  simp only [stateRows2_2_0, final2_2_0, List.map_cons, List.map_nil, patch_states2_2_0_0]
theorem final_states2_2_0 : final2_2_0 = stateRows2_2_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
