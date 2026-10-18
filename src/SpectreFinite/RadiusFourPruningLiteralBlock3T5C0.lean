module

public import SpectreFinite.RadiusFourPruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow3_5_0_0 : List State := [(5,4),(1,4),(0,5),(4,4),(6,4),(4,3),(7,5),(6,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(8,3),(5,5),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(1,1),(0,5),(4,4),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(7,1),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(1,2),(8,4),(0,0),(7,2),(7,4)]
def patch3_5_0_0 : Patch := literalDomain.zip stateRow3_5_0_0
theorem patch_states3_5_0_0 : patch3_5_0_0.map Prod.snd = stateRow3_5_0_0 := by rfl
def stateRow3_5_0_1 : List State := [(5,1),(0,1),(6,2),(8,4),(6,4),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(5,3),(5,5),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(1,1),(0,5),(4,4),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(7,1),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(6,2),(8,4),(0,0),(7,2),(7,4)]
def patch3_5_0_1 : Patch := literalDomain.zip stateRow3_5_0_1
theorem patch_states3_5_0_1 : patch3_5_0_1.map Prod.snd = stateRow3_5_0_1 := by rfl
def stateRow3_5_0_2 : List State := [(5,1),(0,1),(6,2),(8,4),(6,4),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(8,3),(5,5),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(1,1),(0,5),(4,4),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(7,1),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(1,2),(8,4),(0,0),(7,2),(7,4)]
def patch3_5_0_2 : Patch := literalDomain.zip stateRow3_5_0_2
theorem patch_states3_5_0_2 : patch3_5_0_2.map Prod.snd = stateRow3_5_0_2 := by rfl
def final3_5_0 : List Patch := [patch3_5_0_0, patch3_5_0_1, patch3_5_0_2]
def stateRows3_5_0 : List (List State) := [stateRow3_5_0_0, stateRow3_5_0_1, stateRow3_5_0_2]
theorem stateRows_eq3_5_0 : stateRows3_5_0 = final3_5_0.map (List.map Prod.snd) := by
  simp only [stateRows3_5_0, final3_5_0, List.map_cons, List.map_nil, patch_states3_5_0_0, patch_states3_5_0_1, patch_states3_5_0_2]
theorem final_states3_5_0 : final3_5_0 = stateRows3_5_0.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFourPruning
