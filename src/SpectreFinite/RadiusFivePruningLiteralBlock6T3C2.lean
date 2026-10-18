module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart004
public import SpectreFinite.ParentOwnershipFinitePart064
public import SpectreFinite.ParentOwnershipFinitePart065
public import SpectreFinite.ParentOwnershipFinitePart066
public import SpectreFinite.ParentOwnershipFinitePart078

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_3_2_0 : List State := ParentOwnership.parentRow1048
def patch6_3_2_0 : Patch := literalDomain.zip stateRow6_3_2_0
theorem patch_states6_3_2_0 : patch6_3_2_0.map Prod.snd = stateRow6_3_2_0 := by rfl
def stateRow6_3_2_1 : List State := ParentOwnership.parentRow1056
def patch6_3_2_1 : Patch := literalDomain.zip stateRow6_3_2_1
theorem patch_states6_3_2_1 : patch6_3_2_1.map Prod.snd = stateRow6_3_2_1 := by rfl
def stateRow6_3_2_2 : List State := ParentOwnership.parentRow0079
def patch6_3_2_2 : Patch := literalDomain.zip stateRow6_3_2_2
theorem patch_states6_3_2_2 : patch6_3_2_2.map Prod.snd = stateRow6_3_2_2 := by rfl
def stateRow6_3_2_5 : List State := ParentOwnership.parentRow1252
def patch6_3_2_5 : Patch := literalDomain.zip stateRow6_3_2_5
theorem patch_states6_3_2_5 : patch6_3_2_5.map Prod.snd = stateRow6_3_2_5 := by rfl
def stateRow6_3_2_6 : List State := ParentOwnership.parentRow1045
def patch6_3_2_6 : Patch := literalDomain.zip stateRow6_3_2_6
theorem patch_states6_3_2_6 : patch6_3_2_6.map Prod.snd = stateRow6_3_2_6 := by rfl
def stateRow6_3_2_7 : List State := ParentOwnership.parentRow1052
def patch6_3_2_7 : Patch := literalDomain.zip stateRow6_3_2_7
theorem patch_states6_3_2_7 : patch6_3_2_7.map Prod.snd = stateRow6_3_2_7 := by rfl
def stateRow6_3_2_8 : List State := ParentOwnership.parentRow1054
def patch6_3_2_8 : Patch := literalDomain.zip stateRow6_3_2_8
theorem patch_states6_3_2_8 : patch6_3_2_8.map Prod.snd = stateRow6_3_2_8 := by rfl
def stateRow6_3_2_9 : List State := ParentOwnership.parentRow0075
def patch6_3_2_9 : Patch := literalDomain.zip stateRow6_3_2_9
theorem patch_states6_3_2_9 : patch6_3_2_9.map Prod.snd = stateRow6_3_2_9 := by rfl
def stateRow6_3_2_10 : List State := ParentOwnership.parentRow1036
def patch6_3_2_10 : Patch := literalDomain.zip stateRow6_3_2_10
theorem patch_states6_3_2_10 : patch6_3_2_10.map Prod.snd = stateRow6_3_2_10 := by rfl
def stateRow6_3_2_11 : List State := ParentOwnership.parentRow0078
def patch6_3_2_11 : Patch := literalDomain.zip stateRow6_3_2_11
theorem patch_states6_3_2_11 : patch6_3_2_11.map Prod.snd = stateRow6_3_2_11 := by rfl
def final6_3_2 : List Patch := [patch6_3_2_0, patch6_3_2_1, patch6_3_2_2, patch6_3_2_5, patch6_3_2_6, patch6_3_2_7, patch6_3_2_8, patch6_3_2_9, patch6_3_2_10, patch6_3_2_11]
def stateRows6_3_2 : List (List State) := [stateRow6_3_2_0, stateRow6_3_2_1, stateRow6_3_2_2, stateRow6_3_2_5, stateRow6_3_2_6, stateRow6_3_2_7, stateRow6_3_2_8, stateRow6_3_2_9, stateRow6_3_2_10, stateRow6_3_2_11]
theorem stateRows_eq6_3_2 : stateRows6_3_2 = final6_3_2.map (List.map Prod.snd) := by
  simp only [stateRows6_3_2, final6_3_2, List.map_cons, List.map_nil, patch_states6_3_2_0, patch_states6_3_2_1, patch_states6_3_2_2, patch_states6_3_2_5, patch_states6_3_2_6, patch_states6_3_2_7, patch_states6_3_2_8, patch_states6_3_2_9, patch_states6_3_2_10, patch_states6_3_2_11]
theorem final_states6_3_2 : final6_3_2 = stateRows6_3_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
