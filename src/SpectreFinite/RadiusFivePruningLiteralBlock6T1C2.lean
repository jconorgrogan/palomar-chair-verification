module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipFinitePart081
public import SpectreFinite.ParentOwnershipFinitePart082
public import SpectreFinite.ParentOwnershipFinitePart112
public import SpectreFinite.ParentOwnershipFinitePart113

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_1_2_0 : List State := ParentOwnership.parentRow1312
def patch6_1_2_0 : Patch := literalDomain.zip stateRow6_1_2_0
theorem patch_states6_1_2_0 : patch6_1_2_0.map Prod.snd = stateRow6_1_2_0 := by rfl
def stateRow6_1_2_1 : List State := ParentOwnership.parentRow1313
def patch6_1_2_1 : Patch := literalDomain.zip stateRow6_1_2_1
theorem patch_states6_1_2_1 : patch6_1_2_1.map Prod.snd = stateRow6_1_2_1 := by rfl
def stateRow6_1_2_2 : List State := ParentOwnership.parentRow1311
def patch6_1_2_2 : Patch := literalDomain.zip stateRow6_1_2_2
theorem patch_states6_1_2_2 : patch6_1_2_2.map Prod.snd = stateRow6_1_2_2 := by rfl
def stateRow6_1_2_5 : List State := ParentOwnership.parentRow1316
def patch6_1_2_5 : Patch := literalDomain.zip stateRow6_1_2_5
theorem patch_states6_1_2_5 : patch6_1_2_5.map Prod.snd = stateRow6_1_2_5 := by rfl
def stateRow6_1_2_6 : List State := ParentOwnership.parentRow1806
def patch6_1_2_6 : Patch := literalDomain.zip stateRow6_1_2_6
theorem patch_states6_1_2_6 : patch6_1_2_6.map Prod.snd = stateRow6_1_2_6 := by rfl
def stateRow6_1_2_7 : List State := ParentOwnership.parentRow1807
def patch6_1_2_7 : Patch := literalDomain.zip stateRow6_1_2_7
theorem patch_states6_1_2_7 : patch6_1_2_7.map Prod.snd = stateRow6_1_2_7 := by rfl
def stateRow6_1_2_8 : List State := ParentOwnership.parentRow1812
def patch6_1_2_8 : Patch := literalDomain.zip stateRow6_1_2_8
theorem patch_states6_1_2_8 : patch6_1_2_8.map Prod.snd = stateRow6_1_2_8 := by rfl
def stateRow6_1_2_9 : List State := ParentOwnership.parentRow1804
def patch6_1_2_9 : Patch := literalDomain.zip stateRow6_1_2_9
theorem patch_states6_1_2_9 : patch6_1_2_9.map Prod.snd = stateRow6_1_2_9 := by rfl
def stateRow6_1_2_10 : List State := ParentOwnership.parentRow1805
def patch6_1_2_10 : Patch := literalDomain.zip stateRow6_1_2_10
theorem patch_states6_1_2_10 : patch6_1_2_10.map Prod.snd = stateRow6_1_2_10 := by rfl
def stateRow6_1_2_11 : List State := ParentOwnership.parentRow1810
def patch6_1_2_11 : Patch := literalDomain.zip stateRow6_1_2_11
theorem patch_states6_1_2_11 : patch6_1_2_11.map Prod.snd = stateRow6_1_2_11 := by rfl
def final6_1_2 : List Patch := [patch6_1_2_0, patch6_1_2_1, patch6_1_2_2, patch6_1_2_5, patch6_1_2_6, patch6_1_2_7, patch6_1_2_8, patch6_1_2_9, patch6_1_2_10, patch6_1_2_11]
def stateRows6_1_2 : List (List State) := [stateRow6_1_2_0, stateRow6_1_2_1, stateRow6_1_2_2, stateRow6_1_2_5, stateRow6_1_2_6, stateRow6_1_2_7, stateRow6_1_2_8, stateRow6_1_2_9, stateRow6_1_2_10, stateRow6_1_2_11]
theorem stateRows_eq6_1_2 : stateRows6_1_2 = final6_1_2.map (List.map Prod.snd) := by
  simp only [stateRows6_1_2, final6_1_2, List.map_cons, List.map_nil, patch_states6_1_2_0, patch_states6_1_2_1, patch_states6_1_2_2, patch_states6_1_2_5, patch_states6_1_2_6, patch_states6_1_2_7, patch_states6_1_2_8, patch_states6_1_2_9, patch_states6_1_2_10, patch_states6_1_2_11]
theorem final_states6_1_2 : final6_1_2 = stateRows6_1_2.map (List.zip literalDomain) := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
