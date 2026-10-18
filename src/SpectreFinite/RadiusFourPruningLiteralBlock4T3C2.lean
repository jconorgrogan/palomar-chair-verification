module

public import SpectreFinite.RadiusFourPruningLiteralDomain

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_3_2_0 : List State := [(0,4),(5,4),(1,4),(0,5),(4,4),(7,0),(4,3),(7,5),(6,0),(7,1),(7,5),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(8,2),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,4),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2)]
def patch4_3_2_0 : Patch := literalDomain.zip stateRow4_3_2_0
theorem patch_states4_3_2_0 : patch4_3_2_0.map Prod.snd = stateRow4_3_2_0 := by rfl
def stateRow4_3_2_1 : List State := [(0,4),(5,4),(1,4),(0,5),(4,4),(7,0),(4,3),(7,5),(6,0),(7,1),(7,5),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,4),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2)]
def patch4_3_2_1 : Patch := literalDomain.zip stateRow4_3_2_1
theorem patch_states4_3_2_1 : patch4_3_2_1.map Prod.snd = stateRow4_3_2_1 := by rfl
def stateRow4_3_2_2 : List State := [(6,4),(1,2),(7,4),(6,3),(7,2),(3,5),(0,3),(4,1),(0,2),(1,1),(8,1),(0,5),(2,4),(1,3),(5,2),(8,0),(8,3),(5,5),(6,0),(7,1),(6,5),(0,4),(5,4),(1,4),(0,5),(4,4),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(6,0),(7,1),(7,5),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(1,3)]
def patch4_3_2_2 : Patch := literalDomain.zip stateRow4_3_2_2
theorem patch_states4_3_2_2 : patch4_3_2_2.map Prod.snd = stateRow4_3_2_2 := by rfl
def stateRow4_3_2_3 : List State := [(6,4),(1,2),(7,4),(6,3),(7,2),(3,5),(0,3),(4,1),(0,2),(1,1),(8,1),(0,5),(2,4),(1,3),(5,2),(8,0),(8,3),(5,5),(6,0),(7,1),(6,5),(0,4),(5,4),(1,4),(0,5),(4,4),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(6,0),(7,1),(7,5),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,4),(6,3),(7,2),(7,4),(6,3)]
def patch4_3_2_3 : Patch := literalDomain.zip stateRow4_3_2_3
theorem patch_states4_3_2_3 : patch4_3_2_3.map Prod.snd = stateRow4_3_2_3 := by rfl
def final4_3_2 : List Patch := [patch4_3_2_0, patch4_3_2_1, patch4_3_2_2, patch4_3_2_3]
def stateRows4_3_2 : List (List State) := [stateRow4_3_2_0, stateRow4_3_2_1, stateRow4_3_2_2, stateRow4_3_2_3]
theorem stateRows_eq4_3_2 : stateRows4_3_2 = final4_3_2.map (List.map Prod.snd) := by
  simp only [stateRows4_3_2, final4_3_2, List.map_cons, List.map_nil, patch_states4_3_2_0, patch_states4_3_2_1, patch_states4_3_2_2, patch_states4_3_2_3]
theorem final_states4_3_2 : final4_3_2 = stateRows4_3_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFourPruning
