module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart065
public import SpectreFinite.ParentOwnershipFinitePart066
public import SpectreFinite.ParentOwnershipFinitePart078

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_3_1_0 : List State := ParentOwnership.parentRow1046
def patch6_3_1_0 : Patch := literalDomain.zip stateRow6_3_1_0
theorem patch_states6_3_1_0 : patch6_3_1_0.map Prod.snd = stateRow6_3_1_0 := by rfl
def stateRow6_3_1_3 : List State := ParentOwnership.parentRow1047
def patch6_3_1_3 : Patch := literalDomain.zip stateRow6_3_1_3
theorem patch_states6_3_1_3 : patch6_3_1_3.map Prod.snd = stateRow6_3_1_3 := by rfl
def stateRow6_3_1_4 : List State := ParentOwnership.parentRow1053
def patch6_3_1_4 : Patch := literalDomain.zip stateRow6_3_1_4
theorem patch_states6_3_1_4 : patch6_3_1_4.map Prod.snd = stateRow6_3_1_4 := by rfl
def stateRow6_3_1_5 : List State := ParentOwnership.parentRow1055
def patch6_3_1_5 : Patch := literalDomain.zip stateRow6_3_1_5
theorem patch_states6_3_1_5 : patch6_3_1_5.map Prod.snd = stateRow6_3_1_5 := by rfl
def stateRow6_3_1_7 : List State := ParentOwnership.parentRow1061
def patch6_3_1_7 : Patch := literalDomain.zip stateRow6_3_1_7
theorem patch_states6_3_1_7 : patch6_3_1_7.map Prod.snd = stateRow6_3_1_7 := by rfl
def stateRow6_3_1_8 : List State := ParentOwnership.parentRow1062
def patch6_3_1_8 : Patch := literalDomain.zip stateRow6_3_1_8
theorem patch_states6_3_1_8 : patch6_3_1_8.map Prod.snd = stateRow6_3_1_8 := by rfl
def stateRow6_3_1_10 : List State := ParentOwnership.parentRow1064
def patch6_3_1_10 : Patch := literalDomain.zip stateRow6_3_1_10
theorem patch_states6_3_1_10 : patch6_3_1_10.map Prod.snd = stateRow6_3_1_10 := by rfl
def stateRow6_3_1_11 : List State := ParentOwnership.parentRow1259
def patch6_3_1_11 : Patch := literalDomain.zip stateRow6_3_1_11
theorem patch_states6_3_1_11 : patch6_3_1_11.map Prod.snd = stateRow6_3_1_11 := by rfl
def final6_3_1 : List Patch := [patch6_3_1_0, patch6_3_1_3, patch6_3_1_4, patch6_3_1_5, patch6_3_1_7, patch6_3_1_8, patch6_3_1_10, patch6_3_1_11]
def stateRows6_3_1 : List (List State) := [stateRow6_3_1_0, stateRow6_3_1_3, stateRow6_3_1_4, stateRow6_3_1_5, stateRow6_3_1_7, stateRow6_3_1_8, stateRow6_3_1_10, stateRow6_3_1_11]
theorem stateRows_eq6_3_1 : stateRows6_3_1 = final6_3_1.map (List.map Prod.snd) := by
  simp only [stateRows6_3_1, final6_3_1, List.map_cons, List.map_nil, patch_states6_3_1_0, patch_states6_3_1_3, patch_states6_3_1_4, patch_states6_3_1_5, patch_states6_3_1_7, patch_states6_3_1_8, patch_states6_3_1_10, patch_states6_3_1_11]
theorem final_states6_3_1 : final6_3_1 = stateRows6_3_1.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
