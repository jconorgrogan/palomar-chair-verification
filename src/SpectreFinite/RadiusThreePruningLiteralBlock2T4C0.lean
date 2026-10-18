module

public import SpectreFinite.RadiusThreePruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_4_0_0 : List State := [(8,2),(8,0),(7,3),(4,2),(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(4,4),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(8,2),(5,0),(4,5),(7,0),(4,3),(8,4),(0,0),(7,2),(7,4)]
def patch2_4_0_0 : Patch := literalDomain.zip stateRow2_4_0_0
theorem patch_states2_4_0_0 : patch2_4_0_0.map Prod.snd = stateRow2_4_0_0 := by rfl
def final2_4_0 : List Patch := [patch2_4_0_0]
def stateRows2_4_0 : List (List State) := [stateRow2_4_0_0]
theorem stateRows_eq2_4_0 : stateRows2_4_0 = final2_4_0.map (List.map Prod.snd) := by
  simp only [stateRows2_4_0, final2_4_0, List.map_cons, List.map_nil, patch_states2_4_0_0]
theorem final_states2_4_0 : final2_4_0 = stateRows2_4_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusThreePruning
