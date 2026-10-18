module

public import SpectreFinite.RadiusFourPruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_5_0_2 : List State := [(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(0,0),(7,2),(7,4),(1,3),(8,2)]
def patch2_5_0_2 : Patch := literalDomain.zip stateRow2_5_0_2
theorem patch_states2_5_0_2 : patch2_5_0_2.map Prod.snd = stateRow2_5_0_2 := by rfl
def stateRow2_5_0_4 : List State := [(0,4),(5,4),(6,4),(1,2),(8,4),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(0,0),(7,2),(7,4),(6,3),(7,2)]
def patch2_5_0_4 : Patch := literalDomain.zip stateRow2_5_0_4
theorem patch_states2_5_0_4 : patch2_5_0_4.map Prod.snd = stateRow2_5_0_4 := by rfl
def stateRow2_5_0_6 : List State := [(0,4),(5,4),(6,4),(1,2),(8,4),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(0,0),(7,2),(7,4),(1,3),(8,2)]
def patch2_5_0_6 : Patch := literalDomain.zip stateRow2_5_0_6
theorem patch_states2_5_0_6 : patch2_5_0_6.map Prod.snd = stateRow2_5_0_6 := by rfl
def stateRow2_5_0_7 : List State := [(0,4),(5,4),(6,4),(1,2),(8,4),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(0,0),(7,2),(7,4),(1,3),(8,2)]
def patch2_5_0_7 : Patch := literalDomain.zip stateRow2_5_0_7
theorem patch_states2_5_0_7 : patch2_5_0_7.map Prod.snd = stateRow2_5_0_7 := by rfl
def final2_5_0 : List Patch := [patch2_5_0_2, patch2_5_0_4, patch2_5_0_6, patch2_5_0_7]
def stateRows2_5_0 : List (List State) := [stateRow2_5_0_2, stateRow2_5_0_4, stateRow2_5_0_6, stateRow2_5_0_7]
theorem stateRows_eq2_5_0 : stateRows2_5_0 = final2_5_0.map (List.map Prod.snd) := by
  simp only [stateRows2_5_0, final2_5_0, List.map_cons, List.map_nil, patch_states2_5_0_2, patch_states2_5_0_4, patch_states2_5_0_6, patch_states2_5_0_7]
theorem final_states2_5_0 : final2_5_0 = stateRows2_5_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFourPruning
